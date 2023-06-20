{-# LANGUAGE TypeOperators #-}
module Utility(
       trueAtmsInSat,    -- Solver -> [Lit] -> IO [Lit]
       getGCSeqNames,    -- GenClauseSequent Name  -> [Name]
       satAddGLit,       -- Solver -> GenLit Lit -> IO ()
       satAddGClause,     --  Solver -> GenClause Lit  -> IO ()
       satAddGClauses,   -- Solver -> [GenClause Lit] -> IO ()
       -- pretty print
       printfListNl,           --  (a -> Name) -> [a] -> String
       printfForm,             --  (a -> Name) -> Form a -> String
       printfForms,            --  (a -> Name) -> [Form a] -> String
       printfAtms,             --  (a -> Name) ->  [a] -> String
       printfAtmsBrace,        --  (a -> Name) ->  [a] -> String
       printfAtmsSortedBrace,  --  (a -> Name) ->  [a] -> String
       printfGLit,             --  (a -> Name) -> GenLit a -> String
       printfGLits,            --  (a -> Name) -> [GenLit a] -> String
       printfGClause,          --  (a -> Name) -> GenClause a -> String
       printfGClauses,         --  (a -> Name) -> [GenClause a] -> String
       printfGCSeq,            --  (a -> Name) -> GenClauseSequent a -> String
       printfWorld,            --  (a -> Name) ->  World a -> String
       printfModel,            --  (a -> Name) ->  Model a -> String
       -- pretty print of the cache
       printCache,          --  Cache -> String
       printCacheSubst,    --   Cache -> String  -- print the cache with all the substitutions applied
       -- shuffle
       mShuffleSt,          -- RandomGen gen => [a] -> State (Maybe gen) [a]
       mShuffleGCSeqSt      -- RandomGen gen => GenClauseSequent a -> State (Maybe gen)  (GenClauseSequent a)
     )
   where

import MiniSat
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Array.IO
import System.Random  -- https://hackage.haskell.org/package/mwc-random-0.15.0.2/docs/System-Random-MWC.html
import Control.Monad.State

import Language
import ProverTypes


--------------------------------------------------------------------------------
---   ###  SAT SOLVER


trueAtmsInSat :: Solver -> [Lit] -> IO [Lit]
trueAtmsInSat sat univ =
-- atoms from univ which are true in the solver
  do
  vals <- sequence [ (Just True ==) `fmap` modelValue  sat x | x <-  univ  ]
  -- vals = (x,b) where b=True if x is true in sat, b=False  otherwise 
  return  [ x | (x,True) <-  univ `zip` vals ]


getGCSeqNames ::  GenClauseSequent Name  -> [Name]
-- duplication free list of the  the names occurring in the genClauseSequent gcSeq
-- NOTE:  Set.fromList :: Ord a => [a] -> Set    complexity O(n log n)
-- nub ::  Eq a => [a] -> [a]    complexity O(n^2)
getGCSeqNames  gcSeq =
  let ps  =  [ getLitNames c | cs <- classicalGCs gcSeq ,   c <- cs ]
      ips =  [ getLitNames c | cs <- intGCs gcSeq , c <- cs ]
      g = rightAtm gcSeq 
  in Set.toList $ Set.fromList $ (concat ( ps ++ ips ))  ++  [g, false]


gLit_to_lit :: GenLit Lit -> Lit
-- only defined for general literal on the SAT-language corresponding to a classical literal
-- Note that we use the function
-- neg ::  Lit -> Lit
-- of the module MiniSat
gLit_to_lit (At x) = x
gLit_to_lit (Not x) = neg x
-- gLit_to_lit (x :-/->: y) = x


satAddGLit :: Solver -> GenLit Lit -> IO ()
-- add a classical literal (in the SAT-solver language) to the SAT-solver
satAddGLit sat x  =
  addClause sat [gLit_to_lit x]  >> return ()

satAddGClause :: Solver -> GenClause Lit  -> IO Bool
-- add a classical general clause  (in the SAT-solver language) to the SAT-solver
satAddGClause sat  lits  =
  addClause sat (map gLit_to_lit lits) 

satAddGClauses :: Solver -> [GenClause Lit] -> IO ()
-- add a list of classical general clauses  (in the SAT-solver language) to the SAT-solver
satAddGClauses  sat clauses  =
  mapM_ ( satAddGClause sat ) clauses 

  




--------------------------------------------------------------------------------

-- #### PRINT (for trace)

printfListSep :: String -> (a -> String) ->  [a] -> String
-- first argument: separator between elements
printfListSep sep f []   = "" 
printfListSep sep f [x]   = f x
printfListSep sep f (x:xs)   = f x ++ sep ++ printfListSep sep f  xs

printfList :: (a -> String) -> [a] -> String
printfList  = printfListSep ", " 

printfListNl :: (a -> String) -> [a] -> String
printfListNl = printfListSep "\n" 


printfAtms ::   (a -> Name) ->  [a] -> String
printfAtms  f xs = printfList f  xs


printfAtmsSq ::   (a -> Name) ->  [a] -> String
printfAtmsSq  f xs = "[" ++ printfAtms f xs ++ "]"

printfAtmsBrace ::   (a -> Name) ->  [a] -> String
printfAtmsBrace  f xs = "{" ++ printfAtms f xs ++ "}"

printfAtmsSortedBrace ::   (a -> Name) ->  [a] -> String
printfAtmsSortedBrace  f xs =
  let atmNames = map f xs
      nameMindex_pairs = map splitNameIndex atmNames  -- pairs of the kind ("xyz", Just 5), ("abc", Nothing)
      sorted_nameMindex_pairs = List.sort  nameMindex_pairs
  in printfAtmsBrace id (map nameMindex_toString sorted_nameMindex_pairs )

nameMindex_toString :: (Name, Maybe Int) -> String
--   ("xyz", Just 5) |--> "xyz5" ,  ("abc", Nothing) |--> "abc"
nameMindex_toString (name,Nothing) = name
nameMindex_toString (name, Just k) = name ++ show k

 

-- pretty print of formulas 

betweenParens :: String -> String
betweenParens f = "(" ++ f ++ ")"  

--printfForm :: (a -> Name) -> Form a -> String
printfForm :: Show a => (a -> Name) -> Form a -> String   
printfForm pf (Atom atm)  = pf atm

printfForm pf (f1 :&: f2) =
 let sf1 = printfForm pf f1
     sf2 = printfForm pf f2
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,AndOp,NegOp] then sf1 else betweenParens sf1
     sf2' = if (mainLogicalOp (fmap pf f2)) `elem`[ NoOp,AndOp,NegOp] then sf2 else betweenParens sf2
 in sf1'  ++ " & " ++  sf2'

printfForm pf (f1 :|: f2) =
 let sf1 = printfForm pf f1
     sf2 = printfForm pf f2
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,OrOp,NegOp] then sf1 else betweenParens sf1
     sf2' = if (mainLogicalOp (fmap pf f2)) `elem`[ NoOp,OrOp,NegOp] then sf2 else betweenParens sf2
 in sf1'  ++ " | " ++  sf2'


printfForm pf (f1 :=>: FALSE )  =
 let sf1 = printfForm pf f1
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,NegOp] then sf1 else betweenParens sf1
 in "~" ++  sf1'

printfForm pf (f1 :=>: Atom f2 ) | (pf f2) == false  =
 let sf1 = printfForm pf f1
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,NegOp] then sf1 else betweenParens sf1
 in "~" ++  sf1'

printfForm pf (f1 :=>: f2 )  =
 let sf1 = printfForm pf f1
     sf2 = printfForm pf f2
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,NegOp] then sf1 else betweenParens sf1
     sf2' = if (mainLogicalOp (fmap pf f2)) `elem`[ NoOp,NegOp] then sf2 else betweenParens sf2
 in sf1'  ++ " => " ++  sf2'

printfForm pf (f1 :<=>: f2 )  =
 let sf1 = printfForm pf f1
     sf2 = printfForm pf f2
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,NegOp] then sf1 else betweenParens sf1
     sf2' = if (mainLogicalOp (fmap pf f2)) `elem`[ NoOp,NegOp] then sf2 else betweenParens sf2
 in sf1'  ++ " <=> " ++  sf2'
printfForm pf f   = show f -- TRUE | FALSE
  

-- printfForms :: (a -> Name) -> [Form a] -> String
printfForms :: Show a  => (a -> Name) -> [Form a] -> String -- DELETE !!!
printfForms pf forms =
  printfList (printfForm pf ) forms





printCache ::  Cache -> String
printCache cache =
    let nameFormList =  cache_to_sortedNameFormList cache
        items =  map  (\(name,form) ->   name ++ "  |--->  " ++ printfForm id form  )  nameFormList 
    in printfListSep "\n" id items

printCacheSubst ::  Cache  -> String
printCacheSubst cache   =
    let items =  map  (\(name,form) ->   name ++ "  |--->  " ++ printfForm id form  )  (cache_to_nameFormSubstList cache)
    in printfListSep "\n" id items



-- ####################################################

printfGLit ::   (a -> String) -> GenLit a -> String
printfGLit f (At x) =   f x
printfGLit f (Not x) =  "~" ++ f x
printfGLit f (x :-/->: y) =   f x ++ "-/->" ++  f y


printfGLits ::   (a -> String) -> [GenLit a] -> String
rintfGLits f [] = ""
printfGLits f ( x : xs) =
  let sx = printfGLit f x in 
  if null xs then   sx
   else sx ++ ", " ++ printfGLits f xs


  
printfGClause ::  (a -> String) -> GenClause a -> String
printfGClause f [] = "Empty Clause (= False)"
printfGClause f gc = printfListSep " | "  (printfGLit f) gc  


printfGClauses ::  (a -> String) -> [GenClause a] -> String
printfGClauses f [] = ""
printfGClauses f  (gc : gcs ) = 
  let sgc = printfGClause f gc in 
  if null gcs then   sgc
   else sgc ++ "\n" ++ printfGClauses f gcs



printfGCSeq  :: (a -> String) -> GenClauseSequent a -> String
printfGCSeq f gcSet =
  let cGCs  = classicalGCs gcSet
      iGCs =  intGCs gcSet
  in "--    CLASSICAL GEN. CLAUSES (" ++ (show .length)  cGCs ++ "):\n" ++  printfGClauses f cGCs ++ "\n"
     ++ "--   NON_CLASSICAL GEN. CLAUSES (" ++ (show .length)  iGCs ++ "):\n"  ++  printfGClauses f iGCs
      ++ "\n" ++ "--  RIGHT ATOM: " ++   f (rightAtm gcSet)   




-- ########## WORLDS

printfWorld :: (a -> Name) ->  World a -> String
printfWorld f w =
  "W" ++  show (getWIndex w) ++ " = "
  ++ printfAtmsSortedBrace f (getWAtms w )

printfWorlds :: (a -> Name) -> [World a] -> String
printfWorlds  f ws =
  printfListSep  " ;\n   "  (printfWorld f)  ws


printfModel :: (a -> Name) ->  Model a -> String
printfModel f mod = "<< " ++  printfWorlds f  (getWorlds mod)  ++ " >>"

isDigit :: Char -> Bool
isDigit c = (c >= '0') && (c <= '9' ) 

splitName :: Name -> (String,String)
-- split name and index, both as strings
-- "p11" |-> ("p","11") ,  "p123q14" |-> ("p123","14")  , "pqr" |-> ("pqr", "")  
splitName atm =
  let atmRev = reverse atm
      (kRev, nameRev) = span isDigit atmRev 
  in
  (reverse nameRev, reverse kRev)

splitNameIndex :: Name -> (String, Maybe Int)
-- split name and index, where name is a string and index an int
-- "p11" |-> ("p", Just 11) ,  "p123q14" |-> ("p123", Just 14)  , "pqr" |-> ("pqr", Nothing)  
splitNameIndex atm =
  let (name,indexStr) = splitName atm
      mIndex = if null indexStr then Nothing else  Just (read indexStr :: Int)
  in (name, mIndex)    


-- | Randomly shuffle a list
--   /O(N)/
shuffle :: [a] -> IO [a]
shuffle xs =
  do
    let n = length xs
    ar <- newArray n xs
    forM [1..n] $ \i -> do
            j <- randomRIO (i,n)
            vi <- readArray ar i
            vj <- readArray ar j
            writeArray ar j vi
            return vj
  where
    newArray :: Int -> [a] -> IO (IOArray Int a)
    newArray k xs =  newListArray (1,k) xs
-- forM :: (Traversable t, Monad m) => t a -> (a -> m b) -> m (t b)
-- forM :: [int] -> (int -> IO a) -> I0 [a] 


shuffleSt ::RandomGen gen => [a] -> State gen [a]
-- shuffle a generic list
shuffleSt []  = return []
shuffleSt xs  =
  do
    gen0 <- get
    let (k,gen1) = randomR (0,length xs - 1) gen0  -- 0 <= k < length xs
        (ys , zs) = splitAt k xs  --  xs = ys @ zs and length xs = k (thus, zs is not empty)  
    put gen1
    ws <- shuffleSt (ys ++ tail zs) 
    return $ head zs : ws

mShuffleSt ::RandomGen gen => [a] -> State (Maybe gen) [a]
-- if a generator has been defined, shuffle  a generic list; otherwise do nothing.
mShuffleSt xs =
  do
    mgen <- get
    case mgen of
     Just gen0 ->
        do
          let (xs',gen1) = runState  (shuffleSt xs) gen0
          put $ Just gen1
          return xs'
     Nothing -> return xs
          
    
shuffleGCSeqSt :: RandomGen gen => GenClauseSequent a -> State gen  (GenClauseSequent a)  
-- shuffle a sequent
shuffleGCSeqSt  gcSeq =
  do
    cCs' <- shuffleSt ( classicalGCs gcSeq)
    iCs' <- shuffleSt ( intGCs gcSeq )
    return $ gcSeq{ classicalGCs = cCs', intGCs = iCs'}

mShuffleGCSeqSt :: RandomGen gen => GenClauseSequent a -> State (Maybe gen)  (GenClauseSequent a)  
-- if a generator has been defined, shuffle  a sequent; otherwise do nothing.
mShuffleGCSeqSt  gcSeq =
  do
    mgen <- get
    case mgen of
     Just gen0 ->
        do
          let (gcSeq',gen1) = runState  (shuffleGCSeqSt gcSeq) gen0
          put $ Just gen1
          return gcSeq'
     Nothing -> return gcSeq
