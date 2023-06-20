{-# LANGUAGE TypeOperators #-}
module ProverTypes
 where

import MiniSat
import Data.Maybe
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.RWS
import System.Random

import Data.List
import qualified Data.PartialOrd as POrd
import qualified Data.Set as Set
import qualified Data.Map as Map
--import qualified Data.List as List

import Language

-- ########  PROVER STATE ####

data SearchResult  = CountSat | Valid 
data NewWorld_or_NewLearnedGClause =  NewWorld [Lit] | NewLearnedGClause [GenLit Lit]

-- constant fields 
data ProverEnv =
  ProverEnv{
     problemName :: String,     -- the name of the problem to be solved
     universe :: [Lit],         -- all the literals occurring in the problem
     cacheEnv :: Cache,         -- map name |--> simpleForm  used in the clausification
     initGCSeq :: GenClauseSequent Lit,    -- the sequent encoding the problem 
     litToName_map ::  Map.Map Lit  Name ,  -- maps lit |-> atom, with Lit a literal in the SAT-solver language
     traceLevel :: TraceLevel,              -- trace level
     runDebugger ::  Bool                   -- true to debug the execution
    }


mkProverEnv :: String -> [Lit]  -> GenClauseSequent Lit  ->  Map.Map Lit Name  -> TraceLevel -> Bool  ->  Cache ->   ProverEnv
mkProverEnv problName univ  gcSeq  ltToNm_map   traceLev debug cache  =
   ProverEnv{
       problemName = problName,
       universe = univ,
       cacheEnv = cache,
       initGCSeq = gcSeq,
       litToName_map = ltToNm_map,
       traceLevel = traceLev,
       runDebugger = debug
     }


-- fields that can be updated 
data ProverState =
  ProverState{
     solver :: Solver,                  -- the SAT-solver (NOTE: the solver is the same, but it can be updated)
     mRandomGenerator :: Maybe StdGen,  -- monadic random generator (Just randomGenerator, Nothing if the execution is not random)
     countSat :: Int,    -- count the calls to the SAT-solver
     countRest :: Int,   -- count the restarts
     learnedGCs :: [GenClause Lit] ,      -- learned clauses (added to the  SAT-solver during the computation)
     nextWorldIndex :: Int, -- index for the next world
     model :: Model Lit,    -- model )set of worlds) 
     modelsSize :: [Int], -- list of the size (number of worlds) of the generated models just before a restart
--     trace :: Trace Lit,  --  trace  (** NOT USED YET **) ?????
     isValidForm :: Bool -- true iff the input formula is valid
  }

mkProverState :: Solver  -> Maybe StdGen -> ProverState
mkProverState sat mRandomGen  =
   ProverState{
            solver = sat,
            mRandomGenerator =  mRandomGen,
            countSat = 0,
            countRest = 0,
            learnedGCs = [],
            nextWorldIndex = 0,
            model = emptyModel,
            modelsSize = [],
            -- trace = emptyTrace,
            isValidForm = False
            }







-- newtype RWST r w s (m :: * -> *) a
-- A monad transformer adding reading an environment of type r, collecting an output of type w and updating a state of type s to an inner monad m.
-- Here the Writer w is not used 

type ProverConf = RWST ProverEnv () ProverState IO
-- used to represent the Prover state inside the IO monad

-- the name of a literal of the SAT-solver language
-- we assume that the literal is defined
litToName ::   ProverEnv -> Lit ->  Name
litToName  env lit =
     fromJust $ Map.lookup lit (litToName_map env)
     

-- ####### PROVER LOOP #######
--  record  associated with a world


data WorldRec a =
  WorldRec{
     worldInRec ::  World a,         -- world w
     gcsToCheckRec :: [GenClause a], -- general clauses to be checked 
     notImplsCheckedRec :: [GenLit a]  -- a :-/->: b such that w |>^0_W  a :-/->: b
                                       --   where W are the worlds in the current model 
     }




-- make a new WorlRec with empty  checked list  
mkWorldRec :: World Lit -> [GenClause Lit] -> WorldRec Lit
mkWorldRec w gcs =
  WorldRec{worldInRec =  w , gcsToCheckRec = gcs  , notImplsCheckedRec = [] } 

emptyToCheck ::  WorldRec Lit -> Bool
-- true iff thera are no gcs to check
emptyToCheck wRec = null $ gcsToCheckRec wRec


updateWRec :: WorldRec Lit -> GenClause Lit -> [GenLit Lit]  -> WorldRec Lit 
-- update wRec by removing gc from the  gcsToCheckRec list and
-- adding notImpls_new to the notImplsCheckedRec list
updateWRec wRec gc  notImpls_new =
  wRec{
      gcsToCheckRec =  (gcsToCheckRec  wRec)  \\ [gc] ,
      notImplsCheckedRec = notImplsCheckedRec wRec  ++ notImpls_new
      }

-- ##################    MODEL  ########################à
-- A world is a classical interpetation (set of propositional variables)
-- Each world has an int index, only used to pretty print it. 
-- A model is a set of worlds, ordered by the inclusion relation

data World a = Wd(Int, Set.Set a)
  deriving (Eq, Ord, Show)

fmapWd :: (Ord a ,Ord b) => (a -> b) -> (World a -> World b)
fmapWd  f ( Wd(k, xs) ) = Wd ( k, Set.map f  xs )


mkWorld :: Ord a => Int -> [a] -> World a
-- make a new world
mkWorld k atms = Wd( k ,Set.fromList atms )

  
getWIndex :: World a -> Int
-- get the index of a world
getWIndex (Wd(k,_) ) = k
  

getWSetAtms :: World a -> Set.Set a
-- get the propositional variables in a world, as a set
getWSetAtms (Wd(_,xs)) = xs

getWAtms :: World a -> [a]
-- get the propositional variables in a world, as a list
getWAtms (Wd(_,xs)) = Set.toList xs


instance Ord a => POrd.PartialOrd (World a)  where
  (<=) (Wd(k1,s1)) (Wd(k2,s2)) = Set.isSubsetOf s1 s2
  (<)  (Wd(k1,s1)) (Wd(k2,s2)) = Set.isProperSubsetOf s1 s2


-- ordering relations bewteen worlds
(.<.) :: Ord a =>  World a -> World a -> Bool
(.<.)  = (POrd.<) 

(.<=.) :: Ord a =>  World a -> World a -> Bool
(.<=.)  = (POrd.<=) 

(.>.) :: Ord a =>  World a -> World a -> Bool
(.>.)  = (POrd.<) 

(.>=.) :: Ord a =>  World a -> World a -> Bool
(.>=.)  = (POrd.>=) 


-- local realization
infixr 8 .|===.    -- clModel |===  gLit    the general literal gLit    is realized       in the  classical interpretation  clModel   
infixr 8 .|==.     -- clModel |== gc        the general clause gc       is realized       in the  classical interpretation  clModel    
infixr 8 .|=/=.    -- clModel |=/= gc       the general clause gc       is NOT realized   in the  classical interpretation  clModel     

(.|===.) ::  Ord a =>  [a] -> GenLit a -> Bool
clModel  .|===. (At x)   =   x `elem` clModel
clModel  .|===. (Not x)  = not ( x `elem` clModel )
clModel  .|===. ( x :-/->: y)  =  ( x `elem` clModel ) &&  not ( y `elem` clModel ) 

  
(.|==.) ::  Ord a =>  [a] -> GenClause a -> Bool
clModel .|==. xs =
  any  (clModel .|===.) xs

(.|=/=.) ::  Ord a =>  [a] -> GenClause a -> Bool  
clModel  .|=/=. xs = not ( clModel  .|==. xs)



-- atomic forcing
infixr 8  .|--.    --  w .|--. p    atom p is  forced      in w   (p \in w)  
infixr 8  .|-/-.   --  w .|--. p    atom p is  not forced  in w

(.|--.) ::  Ord a =>  World a -> a -> Bool
w  .|--.  x  = Set.member x $ getWSetAtms w 


(.|-/-.) ::  Ord a =>  World a -> a -> Bool
w  .|-/-.  x  = not ( w  .|--.  x )


-- realizability_0 in a world 
infixr 8  .|>.     -- (mod,w)  .|>. gLit      w  |>^0_W  gLit (general literal)    where W is the set of interpretations in  mod
infixr 8  .|>>.    -- (mod,w)  .|>>. gc       w  |>^0_W  gc   (general clause)     where W is the set of interpretations in  mod
    
(.|>.) ::  Ord a =>  (Model a , World a) -> GenLit a -> Bool
(mod,w)  .|>. (At x)  =   w  .|--.  x 
(mod,w)  .|>. (Not x) =   w  .|-/-.  x 
(mod,w)  .|>. ( x :-/->: y) = 
    (not .null )  [ w' | w' <- getWorlds mod, w .<=. w', w' .|--. x, w' .|-/-. y ]


(.|>>.) ::  Ord a =>  (Model a , World a) -> GenClause a -> Bool
(mod,w) .|>>. gc = (not .null) [ gLit | gLit <- gc , (mod,w) .|>. gLit ]

data Model a = Mod( [World a ] ) 
  deriving (Show)

fmapMod :: (Ord a ,Ord b) => (a -> b) -> (Model a -> Model b)
fmapMod  f ( Mod ws ) = Mod (  map (fmapWd f)  ws )


emptyModel :: Model a --Lit
--  the empty model
emptyModel = Mod []

isEmptyModel :: Model a -> Bool
-- check if a model is empty
isEmptyModel (Mod ws) = null ws

mkModel :: [World a ] -> Model a
-- make a new model
mkModel ws = Mod ws

getWorlds ::  Model a -> [World a ] 
-- get the worlds of a model
getWorlds (Mod ws) = ws


addWorld ::Ord a =>  World a -> Model a -> Model a
-- add a world to a model
addWorld w (Mod ws) = Mod $  w : ws


sizeModel :: Model a -> Int 
-- compute the size of a model (= the number of worlds)
sizeModel mod = length ( getWorlds mod)



-- ##################   TRACE   ########################à


data TraceLevel =
  NoTrace
  | TraceLevel_low  -- only basic statistics (number of calls to SAT-solver, restarts) 
  | TraceLevel_medium -- also trace the size of generated models 
  | TraceLevel_high --  print all the traced information
  | TraceLevel_high_with_latex  -- also generate the tex files
   deriving ( Eq, Ord )

{-
data TraceStep a =
  Check( Int, ImplClause a )  
  | AskSatR(Int,Int, a )  
  | AskSatRW(Int,Int, Int,a,a )  
  | NewW( Int, [a] ) 
  | ProvedSat(Int,[a],a) 
  | NewGC(Int,Int, Clause a) 
-}


{-

Check(k, impl):  check the pair < world_k , impl > 
AskSatR(countSat,countRest, right ):    R_countRest |-- c right ?
AskSatRW(countSat,countRest, k , a, b ):  R_countRest, world_k, a |-- c b ?
NewWorld(k, atms ):  generated a new world of index k from atms  
ProvedSat(countRest,assumps,right) --  R_countRest, assmups |--c  right
NewClause(countSat,countRest, phi) --  phi is anew clauses   

-}

{-
instance Functor TraceStep where
  fmap f (Check(k,ic)) = Check( k ,mapImplClause f ic )
  fmap f  (AskSatR(cntSat,cntRest,right)) = AskSatR (cntSat,cntRest, f right)
  fmap f  (AskSatRW(cntSat,cntRest, wk,a, right)) = AskSatRW (cntSat,cntRest,wk,f a,  f right)
  fmap f (NewW (k, xs) ) = NewW( k, map f xs)
  fmap f (ProvedSat(k,xs,right)) = ProvedSat(k , map f xs , f right)
  fmap f ( NewGC(cntSat, cntRest,c) ) = NewGC(cntSat,cntRest, fmap f c)



traceName ::  ProverEnv -> ProverState -> Trace Name
traceName env pst = fmap (litToName env) (trace pst) 



data Trace a = Trace [TraceStep a]


instance Functor Trace where
  fmap f (Trace steps) = Trace( map (fmap f) steps )

emptyTrace :: Trace a --Lit
emptyTrace = Trace []

addStep :: TraceStep a ->   Trace a -> Trace a
addStep step (Trace steps) = Trace (step: steps) 

addSteps :: [TraceStep a] ->   Trace a -> Trace a
addSteps [] tr = tr
addSteps (s1 :steps) tr =
  addStep s1  (addSteps steps tr)

getSteps :: Trace a -> [TraceStep a]
getSteps (Trace steps) = reverse steps

-}
