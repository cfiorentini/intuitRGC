{-# LANGUAGE TypeOperators #-}

-- Claesse & Rosem clausification
module ClausifyClaessenRosen
  (
    clausifyFormsClaessenRosen  --  ClausificationType -> Bool -> [Form Name] ->   (Cache, GenClauseSequent Name)
  )
 where


import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Control.Monad.State
import Debug.Trace

import Language
import ClausifyCommon


clausifyFormsClaessenRosen :: ClausificationType -> Bool -> [Form Name] ->   (Cache, GenClauseSequent Name)
-- Clausify a list of formulas
clausifyFormsClaessenRosen  cType clausDebug forms =
  let
    finalClausSt = execState (mclausifyForms forms) (mkClausState cType clausDebug  0)
    finalCache = clausCache_simpleForm_name finalClausSt 
    cGcs  = Set.toList $ clausClGCset   finalClausSt 
    iGcs =  Set.toList $ clausIntGCset  finalClausSt
    (iGcs_notImpl,iGcs_proper) = partition (\iGc -> length iGc == 1) iGcs
    -- iGcs_notImpl = iGcs of the form a -/-> b
    -- iGcs_proper  = iGcs of the form c V (a -/-> b) 
    (count, cGcs1,iGcs1) = reduceIGCs iGcs_proper
    gcSet =  GenClauseSequent{ classicalGCs = cGcs `union` cGcs1 ,
                               intGCs =  iGcs1 ++ iGcs_notImpl ,
                               rightAtm =  mainGoalName}
  in  ( invertMap finalCache  ,  gcSet )   

invertMap :: (Ord a, Ord b) => Map.Map a b -> Map.Map b a
invertMap m =
   Map.fromList $ map swap (Map.toList m )
   where swap(a,b) = (b,a)



mclausifyForms ::  [Form Name] ->  State ClausState ()
-- clausification of a list of formulas
mclausifyForms  fs =mapM_  ( clausifyForm . simplify ) fs
 -- sequence_ [ clausifyForm (simplify f) | f <- fs ] 



{-

REDUCE NON-CLASSICAL GENERAL CLAUSES WITH THE SAME NOT-IMPL LITERA

Clauses with the same antecedent are reduced as follows:

 c1 v ( a -/-> b) , ... , cn v ( a -/-> b)

with n >= 2 is reduced to

   ~c1 v newAtm, ... , ~cn v newAtm ,  ~newAtm  v (a -/-> b)


where newAtm is a new propositional variable

-}


type SameAnt =  ( GenLit Name, [Name] )
--    ( (a :-/->: b), [c1,..c_n] ) represent the list of igcs
--    c1 v(a :-/->: b) , ... ,   c1 v(a :-/->: b)





reduceIGCs ::  [GenClause Name] ->   (Int,[GenClause Name], [GenClause Name])
--  ** Same strategy as ClaessenRosen **
{-
Return (tot,cGcs1,iIs1) where:
tot: total amount of clauses with the same antecedent
cGcs1:  new classical clauses (of the form ~ck v newAtm ) generated during the process
iGcs1:  new implication general clauses obtained after reduction
*NOTE*
o Whenever we add the igc c v (a-/->b), we also add ~b v c (equivalent to b -> c) 
o if no iGc is reduced, iGcs1 is in general a permutation of iGcs 

-}

reduceIGCs iGcs =  
  let pairs = [  ( a :-/->: b , c) | iGc <- iGcs,  a :-/->: b <- iGc, At c <- iGc ] 
      sames = Map.toList (Map.fromListWith (++) [  (a :-/->: b, [c]) |   ( a :-/->: b , c)   <- pairs ] )
  in evalState ( mreduceIGCs sames )  (0,0,[],[])


mreduceIGCs :: [SameAnt]
  -> State (Int,Int,[GenClause Name],[GenClause Name])  (Int,[GenClause Name], [GenClause Name])
-- state: next index, number of reduced ics, cs, ics

mreduceIGCs [] =
  do 
    (n,count,cGcs,iGcs) <- get
    return (count,cGcs,iGcs) 

mreduceIGCs ( (a :-/->: b  ,[c])  : sames) =
  do
  (n,count,cGcs, iGcs) <- get
  let newGcs = if isFalse b then  cGcs else [ Not b, At c ]  : cGcs
  put (n, count, newGcs ,  [ At c, a :-/->: b ]  : iGcs )
  mreduceIGCs sames



mreduceIGCs ( (  a :-/->: b ,xs)  : sames) =
--  length xs >= 2 
  do
  (n,count,cGcs, iGcs) <- get
  let k = length xs
      newAtm = "$q" ++ show n
      cGcs1 = [ [ Not newAtm, At x] | x <- xs ] ++ cGcs
      newGcs = if isFalse b then  cGcs1 else [ Not b,  At newAtm ] : cGcs1
  put (n + 1, count + k,  newGcs ,  [  At newAtm , a :-/->: b  ] :  iGcs )
  mreduceIGCs sames



--------------------------------------------------------
-- ORIGINAL CLAUSIFICATION PROCEDURE BY CLAESSEN&ROSEN

-- build the formulas equivalent to the input formulas
 
goalify :: [Input (Form Name)] -> [Form Name]
goalify []                            = []
goalify (Input s Axiom f       : inps) = f : goalify inps
goalify (Input s Conjecture f : inps) =
  case f of
    a :=>: b -> a : goalify (Input s Conjecture b : inps)
    _        -> (f :=>: Atom mainGoalName) : goalify inps


--------------------------------------------------------------------------------


-- CLAUSIFICATION OF A FORMULA
-- We assume that the formula is simplified
-- The clausification procedure updates the state
clausifyForm ::  Form Name -> State ClausState ()
-- any formula
clausifyForm TRUE        =
  do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> clausifyForm TRUE " ) 
    return ()   -- do nothing 

clausifyForm FALSE       =
  do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> clausifyForm FALSE " ) 
    addClGClause []   

clausifyForm (Atom a)    =
  do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> clausifyForm (Atom a)\nARG\t" ++ show (Atom a) ) 
    addClGClause [At a] 

clausifyForm (f1 :&: f2) =
  do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> clausifyForm (f1 :&: f2)\nARG\t" ++ show (f1 :&: f2) ) 
    clausifyForm f1 >> clausifyForm f2
  

 
clausifyForm (f1 :|: f2)   =
  do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> clausifyForm (f1 :|: f2)\nARG\t" ++ show (f1 :|: f2) ) 
    clausifyOr [] [f1,f2]

clausifyForm (f1 :=>: f2)  =
  do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> clausifyForm (f1 :=>: f2)\nARG\t"++ show (f1 :=>: f2) ) 
    clausifyImpl f1 f2   -- note that f1 /= FALSE


clausifyForm (f1 :<=>: f2) =
  do
    cSt <- get
    p1 <- nameEquivWith f1
    p2 <- nameEquivWith f2
    ( when (clausDebug cSt) $
            do
              let msg = ">>> clausifyForm (f1 :<=>: f2)\nARG\t" ++ show (f1 :<=>: f2)
                        ++ "\n\tp1 = nameEquivWith f1 ---> " ++ show p1
                        ++ "\n\tp2 = nameEquivWith f2 ---> " ++ show p2     
              traceM msg
      ) -- end when
    -- we add the clauses
    --    p1 => p2 , p2 => p1
    --   ~p1 | p2  , ~p2 | p1
    addClGClauses [ [Not p1, At p2] , [Not p2, At p1] ] 



clausifyOr :: [Name] -> [Form Name] -> State ClausState ()
-- clausifyOr [p1 .. pm] [f1 ... fn]  (with p1 ... pm atoms, f1 .. fn any formulas)
-- clausify  the formula
--   p1 | ... | pm | f1 ... | fn
clausifyOr ps [] =  addClGClause (map At ps) 
clausifyOr ps ((f1 :|: f2) : fs) =  clausifyOr ps (f1 : f2 : fs)
clausifyOr ps (f1 : fs) =
  do
    cSt <- get
    p1 <-
      case  clausType cSt of
        ClaessenRosenClausification -> nameThatImplies f1
        ClaessenRosenClausificationStrong  -> nameEquivWith   f1
    clausifyOr (p1:ps) fs


clausifyImpl :: Form Name -> Form Name -> State ClausState ()
-- clausifyImpl f1 f2
-- clausify the formula f1 => f2
-- We assume f1 /= FALSE
clausifyImpl (Atom a)  (Atom b)   =
  do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> clausifyImpl (Atom a) (Atom b)\nARGS\t" ++ show a ++ " , " ++ show b ) 
    -- add a => b
    -- ~a | b
    addClGClause [ Not a, At b]

clausifyImpl (Atom a)  FALSE   =
  do
    cSt <- get
    when (clausDebug cSt) $
       traceM ( ">>> clausifyImpl (Atom a) FALSE\nASRG\t" ++ show a ) 
      -- add ~a
    addClGClause [ Not a ]


clausifyImpl (Atom a)  (f1 :&: f2)  =
  do
    cSt <- get
    when (clausDebug cSt) $
       traceM ( ">>> clausifyImpl (Atom a) (f1 :&: f2)\nARGS\t" ++ show a  ++ " , "  ++ show (f1 :&: f2) ) 
    clausifyImpl (Atom a) f1 
    clausifyImpl (Atom a) f2

clausifyImpl (f1 :|: f2) (Atom b)   =
   do
     cSt <- get
     when (clausDebug cSt) $
       traceM ( ">>> clausifyImpl (f1 :|: f2) (Atom b)\nARGS\t" ++ show (f1 :|: f2)  ++ " , "  ++ show (Atom b) ) 
     clausifyImpl f1 (Atom b)
     clausifyImpl f2 (Atom b)

clausifyImpl (f1 :|: f2) FALSE  =
   do
     cSt <- get
     when (clausDebug cSt) $
       traceM ( ">>> clausifyImpl (f1 :|: f2) FALSE\nARG\t" ++ show (f1 :|: f2)   ) 
     clausifyImpl f1 FALSE
     clausifyImpl f2 FALSE

clausifyImpl f1  (f2 :=>: f3) =
  do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> clausifyImpl  f1  (f2 :=>: f3)\nARGS\t" ++ show f1  ++ " , "  ++ show (f2 :=>: f3) ) 
    clausifyImpl (f1 :&: f2) f3

clausifyImpl (f1 :=>: FALSE) FALSE =
-- f1 /= FALSE, 
  do
    cSt <- get
    p1 <-
      case  clausType cSt of
        ClaessenRosenClausification -> nameThatImplies f1
        ClaessenRosenClausificationStrong  -> nameEquivWith   f1
     --  add  (p1 => false ) => false
     --  false v (p1 -/-> false)   equivalent to  p1 -/-> false
    ( when (clausDebug cSt) $
            do
              let msg =  ">>> clausifyImpl (f1:=>: FALSE)  FALSE\nARG\t"++ show (f1 :=>: FALSE) 
                      ++ "\n\tp1 = name(ThatImplies|EquivWith) f1 ---> " ++ show p1
              traceM msg
      ) -- end whe 
    addIntGClause [ p1 :-/->: false ]


clausifyImpl (f1 :=>: f2)  FALSE =
-- f1 /= FALSE, f2 /=FALSE  
  do
    cSt <- get
    p1 <-
      case  clausType cSt of
        ClaessenRosenClausification -> nameThatImplies f1
        ClaessenRosenClausificationStrong  -> nameEquivWith   f1
    p2 <-
      case  clausType cSt of
        ClaessenRosenClausification -> nameImpliedBy f2
        ClaessenRosenClausificationStrong  -> nameEquivWith   f2
    ( when (clausDebug cSt) $
            do
              let msg = ">>> clausifyImpl (f1:=>: f2)  FALSE, where f2 /=FALSE\nARG\t"++ show (f1 :=>: f2)
                      ++ "\n\tp1 = name(ThatImplies|EquivWith) f1 ---> " ++ show p1
                      ++ "\n\tp2 = name(ImpliedBy|EquivWith) f2 ---> " ++ show p2
              traceM msg
      ) -- end when     
    --  add  (p1 => p2 ) => false
    --  false v (p1 -/-> p2)    equivalent to  p1 -/-> p2
    addIntGClause [ p1 :-/->: p2 ]
  
-- f1 /= FALSE,  f3 =/= FALSE
clausifyImpl (f1 :=>: FALSE)  f3 =
  do
    cSt <- get
    p1 <-
      case  clausType cSt of
        ClaessenRosenClausification -> nameThatImplies f1
        ClaessenRosenClausificationStrong  -> nameEquivWith   f1
    p3 <-
      case  clausType cSt of
        ClaessenRosenClausification -> nameThatImplies f3
        ClaessenRosenClausificationStrong  -> nameEquivWith   f3
    ( when (clausDebug cSt) $
            do
              let msg =  ">>> clausifyImpl  (f1 :=>: FALSE)  f3, where f3 =/= FALSE\nARGS\t"++ show (f1 :=>: FALSE) ++ " , " ++ show f3
                    ++ "\n\tp1 = name(ThatImplies|EquivWith) f1 ---> " ++ show p1
                    ++ "\n\tp3 = name(ThatImplies|EquivWith) f3 ---> " ++ show p3
              traceM msg
      ) -- end when   
     --  add  (p1 => false ) => p3
     --  p3 v (p1 -/-> false ) 
    addIntGClause [ At p3, p1 :-/->: false ]

-- f1 /= FALSE, f2 /=FALSE, f3 =/= FALSE
clausifyImpl (f1 :=>: f2)  f3 =
  do
    cSt <- get
    p1 <-
      case  clausType cSt of
        ClaessenRosenClausification -> nameThatImplies f1
        ClaessenRosenClausificationStrong  -> nameEquivWith   f1
    p2 <-
      case  clausType cSt of
        ClaessenRosenClausification -> nameImpliedBy f2
        ClaessenRosenClausificationStrong  -> nameEquivWith   f2
    p3 <-
      case  clausType cSt of
        ClaessenRosenClausification -> nameThatImplies f3
        ClaessenRosenClausificationStrong  -> nameEquivWith   f3
    ( when (clausDebug cSt) $
            do
              let msg =  ">>> clausifyImpl (f1 :=>: f2) f3, where  f2 /=FALSE, f3 /= FALSE\nARGS\t" ++ show (f1 :=>: f2) ++ " , " ++ show f3
                    ++ "\n\tp1 = name(ThatImplies|EquivWith) f1 ---> " ++ show p1 
                    ++ "\n\tp2 = name(ImpliedBy|EquivWith) f2 ---> " ++ show p2
                    ++ "\n\tp3 = name(ThatImplies|EquivWith) f3 ---> " ++ show p3 
              traceM msg
              
      ) -- end when      
     --  add  (p1 => p2 ) => p3
     --  p3 v (p1 -/-> p2) 
    addIntGClause [ At p3, p1 :-/->: p2 ]

-- f1 /= FALSE 
clausifyImpl f1 FALSE  =
  do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> clausifyImpl f1 FALSE\nARG\t" ++ show f1 ++ " , FALSE"  ) 
    p1s <- namesAnd f1  -- p1_1 ... p1_m
    -- add  ( p1_1 & ... & p1_m ) => false
    --      ~p1_1 | ... | ~p1_m 
    addClGClause  ( map Not p1s ) 



-- f1 /= FALSE, f2 /= FALSE
clausifyImpl f1 f2  =
  do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> clausifyImpl f1 f2, where  f2 /= FALSE\nARGS\t" ++ show f1 ++ " , " ++ show f2 ) 
    p1s <- namesAnd f1  -- p1_1 ... p1_m
    p2s <- namesOr  f2  -- p2_1 ... p2_n
     -- add  ( p1_1 & ... & p1_m ) => ( p2_1 |...| p2_n )
     --    ~p1_1 | ... | ~p1_m | p2_1 | ... | p2_n
    addClGClause  ( (map Not p1s) ++  (map At  p2s) )


namesAnd :: Form Name ->  State ClausState  [Name]
-- namesAnd (f1 & ... & fn)
-- [p1, ...,  pn] such that pk is a name for fk, for every 1 <= k <= n
namesAnd (f1 :&: f2) =
  do p1s <- namesAnd f1
     p2s <- namesAnd f2
     return (p1s ++ p2s)
namesAnd f =
  do
    cSt <- get
    p <-
      case  clausType cSt of
        ClaessenRosenClausification -> nameImpliedBy f
        ClaessenRosenClausificationStrong  -> nameEquivWith   f
    return [p]

namesOr :: Form Name -> State ClausState  [Name]
-- namesOr (f1 | ... | fn)
-- [p1, ..., pn] such that pk is a name for fk, for every 1 <= k <= n
namesOr (f1 :|: f2) =
  do p1s <- namesOr f1
     p2s <- namesOr f2
     return (p1s ++ p2s)
namesOr f  =
  do
    cSt <- get
    p <-
      case  clausType cSt of
        ClaessenRosenClausification -> nameThatImplies f
        ClaessenRosenClausificationStrong  -> nameEquivWith   f
    return [p]


