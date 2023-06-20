{-# LANGUAGE TypeOperators #-}
module Language
 where


import Data.Maybe
import Data.List
import qualified Data.PartialOrd as POrd
import qualified Data.Set as Set
import qualified Data.Map as Map



-- ######### FORMULA ##########

type Name = String
type GoalName = Name

-- some constants

false :: Name
false = "$false"

isFalse :: Name -> Bool
isFalse p = p == false

true :: Name
true = "$true"

mainGoalName :: Name
mainGoalName = "$goal"

isNewName :: Name -> Bool
isNewName p =
  head p == '$'


data Form a 
  = TRUE
  | FALSE
  | Atom a
  | (Form a) :&: (Form a)
  | (Form a) :|: (Form a)
  | (Form a ) :=>: (Form a)
  | (Form a) :<=>: (Form a)
   deriving ( Eq, Ord )


instance (Show a) =>  Show (Form a) where
  show (Atom a)    = show a
  show (p :&: q)   = "(" ++ show p ++ " & " ++ show q ++ ")"
  show (p :|: q)   = "(" ++ show p ++ " | " ++ show q ++ ")"
  show (p :=>: q)  = "(" ++ show p ++ " => " ++ show q ++ ")"
  show (p :<=>: q) = "(" ++ show p ++ " <=> " ++ show q ++ ")"
  show TRUE        =  "TRUE"  --- "$true"
  show FALSE       =  "FALSE" -- "$false"


instance Functor Form where
  fmap g (Atom p)    = Atom (g p)
  fmap g (f1 :&: f2)   = (fmap g f1)  :&:  (fmap g f2 )
  fmap g (f1 :|: f2)   = (fmap g f1)  :|:  (fmap g f2 )
  fmap g (f1 :=>: f2)  = (fmap g f1)  :=>:  (fmap g f2 )
  fmap g (f1 :<=>: f2) = (fmap g f1)  :<=>:  (fmap g f2 )
  fmap g TRUE        =  TRUE
  fmap g FALSE       =  FALSE 



data SimpleForm 
  = Name :&&: Name
  | Name :||: Name
  | Name :==>: Name
  | Name :<==>: Name
 deriving ( Eq, Ord, Show )


simpleFormToForm :: SimpleForm -> Form Name
simpleFormToForm (n1 :&&: n2)   = (Atom n1)  :&: (Atom n2)
simpleFormToForm (n1 :||: n2)   = (Atom n1)  :|: (Atom n2)
simpleFormToForm (n1 :==>: n2)  = (Atom n1)  :=>: (Atom n2)
simpleFormToForm (n1 :<==>: n2) = (Atom n1)  :<=>: (Atom n2) 



type Cache = Map.Map Name SimpleForm 
-- map atom |--> simple form, used in clausification

emptyCache :: Cache
emptyCache =  Map.empty 

cache_to_nameFormList :: Cache -> [(Name, Form Name)]
cache_to_nameFormList cache =
  map ( \(name,sf ) -> ( name, simpleFormToForm sf) )  (Map.toList cache)

cache_to_sortedNameFormList :: Cache -> [(Name, Form Name)]
cache_to_sortedNameFormList  cache =
  sortOn (indexNewName .fst ) ( cache_to_nameFormList cache)

cacheSize :: Cache -> Int
cacheSize  = Map.size 


indexNewName  :: Name -> Int
-- newName: $p0, $p1, ....
-- $p0 |-> 0,   $p1 |-> 1,  $p10 |-> 10, ...
indexNewName newName =
  -- read $ fromJust $ stripPrefix "$p" newName
  read $ fromMaybe "-1" $ stripPrefix "$p" newName  -- -1 in case of error



-- used to represent TPTP formulas
data Input a = Input Name FormRole a
 deriving ( Eq, Ord )

instance Show a => Show (Input a) where
  show (Input name role x) =
    "fof(" ++ name ++ ", " ++ show role ++ ", " ++ show x ++ " )."

data FormRole =
  Axiom
  | Conjecture
 deriving ( Eq, Ord )

instance Show FormRole where
  show Axiom       = "axiom"
  show Conjecture = "conjecture"


multiAnd  ::  [Form a] -> Form a
-- f1 .. fn  -- >   f1 & ... & fn
multiAnd [] = TRUE
multiAnd (f : fs) =
  if null fs then f
  else f :&: multiAnd fs

multiOr  ::  [Form a] -> Form a
-- f1 .. fn  -- >   f1 v ... v fn
multiOr [] = FALSE
multiOr (f : fs) =
  if null fs then f
  else f :|: multiOr fs




buildImplication  ::  [Form a] -> [Form a] ->  Form a
-- [f1 .. fm] [g1..gn] |-->   (f1 & .. & fm) => (g1 v .. v gn)  
buildImplication fs gs =
  if null fs then multiOr gs
  else
    (multiAnd fs) :=>: (multiOr gs)

buildInputForm :: [Input (Form a)] -> Form a
{-

Given a list of input formulas

 (Input  _ Axiom a1)      ...      (Input _ Axiom an) , (Input  _ Conjecture c) 

(in any order) return the formula

  a1 & .. & an => c   

ASSUMPTION: there is one Conjecture

-}
buildInputForm inputForms =
  let fs = [ f | (Input _  Axiom f) <- inputForms ]
      g =  head [ f | (Input _  Conjecture f) <- inputForms ]
  in buildImplication  fs [g]

parseInputForm :: [Input (Form a)] -> ([Form a], Form a)

{-

Given a list of input formulas

 (Input  _ Axiom a1)      ...      (Input _ Axiom am) ,
 (Input  _ Conjecture ( b1 & ... & bn =>  c )      // just one conjecture

(in any order) return pair of formulas

(  [a1, .. , am, b1 ... & bn] ,  c  )   

representing the formula

  a1 & .. & am & b1 ... & bn =>  c 

ASSUMPTION: there is one Conjecture

-}
parseInputForm inputForms =
  let as = [ f | (Input _  Axiom f) <- inputForms ]
      g =  head [ f | (Input _  Conjecture f) <- inputForms ]
      (bs,c) = extractAntecedents g
  in   (  as ++ bs  , c   )

extractAntecedents :: Form a ->  ([Form a], Form a)
extractAntecedents ( a :=>: b ) =
  let (cs, c) = extractAntecedents b
  in  ( (a : cs) , c )
 
extractAntecedents f = ([],f) 

data LogicalOp = NoOp | NegOp | AndOp | OrOp | ImplOp | IffOp 
  deriving Eq

mainLogicalOp :: Form Name-> LogicalOp

mainLogicalOp  f | f == TRUE || f == FALSE = NoOp
mainLogicalOp (Atom _) = NoOp 
mainLogicalOp (f1 :&: f2 ) = AndOp
mainLogicalOp (f1 :|: f2 ) = OrOp
mainLogicalOp (f1 :=>: FALSE ) = NegOp
mainLogicalOp (f1 :=>: Atom f2 ) | f2 == false = NegOp
mainLogicalOp (f1 :=>: f2 ) = ImplOp
mainLogicalOp (f1 :<=>: f2 ) = IffOp


-- general literal
data GenLit a =
  At a
  | Not a -- not a
  | a :-/->:   a  -- not implication
 deriving ( Eq, Ord )

instance Functor GenLit where
  fmap f (At x)       = At (f x)
  fmap f (Not x)      = Not (f x)
  fmap f (x :-/->: y) = (f x) :-/->: (f y) 

instance Show a => Show (GenLit a) where
  show (At x) =  show x
  show (Not x) = "~" ++ show x
  show  (x :-/->: y) = show x ++ "-/->" ++ show y

isAtGLit :: GenLit a -> Bool
-- check if a general literal is an atom 
isAtGLit (At _) = True
isAtGLit _ = False


getLitNames :: GenLit Name -> [Name]
-- get the names in a general literal
getLitNames (At s) = [s]
getLitNames (Not s) = [s]
getLitNames (s1 :-/->: s2) = [s1, s2]


-- general clause
type GenClause a =  [GenLit a] 


isClassicalGenClause :: GenClause a -> Bool
-- check if a general clause is classical (namely, it does not contain  :-/->: )
isClassicalGenClause gc = null [   a :-/->: b   | (a :-/->: b)  <- gc ]


nonTrivialIntGC :: GenClause a -> Bool
-- check if a general clause is not trvial, namely it contains at least 2 nonImpl general literals
nonTrivialIntGC xs = ( length [ x :-/->: y | (x:-/->:y)  <- xs ] > 1 )
                 ||  ( length [ Not x  |  (Not x)  <- xs ] > 0 )
                 ||  ( length [ At x   |  (At x)  <- xs ] > 1 )



-- sequent Gamma => rightAtm
-- Gamma = classicalGCs +  intGCs
data GenClauseSequent a =
  GenClauseSequent{
     classicalGCs:: [GenClause a], -- classical gcs in      Gamma
     intGCs :: [GenClause a],      -- intuitionistic gcs in Gamma  
     rightAtm ::  a
  } 


instance Functor GenClauseSequent where
  fmap f (GenClauseSequent{ classicalGCs = ps, intGCs = is , rightAtm = g }) =
    let mmfmap = map .map .fmap
    in GenClauseSequent{classicalGCs = mmfmap f  ps , intGCs = mmfmap f is , rightAtm =  f g }

mkGenClauseSequent :: [GenClause a] -> a ->  GenClauseSequent a
-- make a general clause
mkGenClauseSequent gcs r =
  let (cGcs, iGcs ) = partition isClassicalGenClause gcs
  in GenClauseSequent{classicalGCs = cGcs , intGCs = iGcs , rightAtm = r }

-- type of a clausification
data ClausificationType = WeakClausification | StrongClausification | ClaessenRosenClausification |  ClaessenRosenClausificationStrong
  deriving Eq

instance Show  ClausificationType where
  show  WeakClausification =  "Weak clausification"
  show  StrongClausification =  "Strong clausification"
  show  ClaessenRosenClausification =  "Claessen&Rosen clausification (weak)"
  show  ClaessenRosenClausificationStrong =  "Claessen&Rosen clausification, strong clausification"


isClaessenRosenClausificationType ::  ClausificationType -> Bool
isClaessenRosenClausificationType cType =
  cType `elem` [ ClaessenRosenClausification,  ClaessenRosenClausificationStrong ]

isGeneralClausesClausificationType cType =
   cType `elem` [  WeakClausification,   StrongClausification  ]


type Substitution = Map.Map Name (Form Name)


-- substitutions
-- used to build the map atom |--> formula in a cache
applySubst :: Substitution -> Form Name -> Form Name

applySubst subst TRUE = TRUE
applySubst subst FALSE = FALSE

applySubst subst (Atom a) =
  case Map.lookup a subst of
      Just f -> applySubst subst f
      Nothing -> Atom a

applySubst subst (f1 :&: f2) =
  (applySubst subst f1 ) :&: (applySubst subst f2)

applySubst subst (f1 :|: f2) =
  (applySubst subst f1 ) :|: (applySubst subst f2)

applySubst subst (f1 :=>: f2) =
  (applySubst subst f1 ) :=>: (applySubst subst f2)

applySubst subst (f1 :<=>: f2) =
  (applySubst subst f1 ) :<=>: (applySubst subst f2)


cache_to_nameFormSubstList ::  Cache ->   [(Name, Form Name)]
--  list (name,form) such that  form is the formula equivalent to name
cache_to_nameFormSubstList  cache   =
  let nameFormList = cache_to_sortedNameFormList cache
      subst = Map.fromList  nameFormList
  in  map (\(name,form) ->  (name, (applySubst subst form)) ) nameFormList

cache_to_subst  :: Cache   -> Substitution
-- substitution     extracted from the cache
cache_to_subst  = Map.fromList . cache_to_nameFormSubstList  



