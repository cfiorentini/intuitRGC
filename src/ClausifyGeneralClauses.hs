{-# LANGUAGE TypeOperators #-}
module ClausifyGeneralClauses
  (  clausifyForms   -- ClausificationType ->  [Form Name] ->   (Cache, GenClauseSequent Name)
  )
 where


import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State
import Debug.Trace

import Language
import ClausifyClaessenRosen
import ClausifyCommon




-- #### MAIN  #####



clausifyForms :: ClausificationType -> Bool ->  [Form Name]  ->  (Cache, GenClauseSequent Name)
-- Clausify a list of formulas
-- cType: clausidication type
-- clausDebug: True to debug the clausification proces 
clausifyForms cType clausDebug forms | isClaessenRosenClausificationType cType  =
  clausifyFormsClaessenRosen  cType clausDebug forms


clausifyForms cType clausDebug forms  =
  let
    finalClausSt = execState (mclausifyForms forms) (mkClausState cType clausDebug   0)
    finalCache = clausCache_simpleForm_name finalClausSt 
    cGcs  = Set.toList $ clausClGCset   finalClausSt 
    iGcs =  Set.toList $ clausIntGCset  finalClausSt
    gcSet =  GenClauseSequent{ classicalGCs = cGcs, intGCs = iGcs, rightAtm =  mainGoalName}
  in  ( invertMap finalCache  ,  gcSet )   

invertMap :: (Ord a, Ord b) => Map.Map a b -> Map.Map b a
invertMap m =
   Map.fromList $ map swap (Map.toList m )
   where swap(a,b) = (b,a)



mclausifyForms ::  [Form Name] ->  State ClausState ()
-- clausification of a list of formulas
mclausifyForms  fs = mapM_  ( clausifyForm . simplify ) fs
 -- sequence_ [ clausifyForm (simplify f) | f <- fs ] 


---------------------------------------------------------------
-- CLAUSIFICATION OF A FORMULA
-- We assume that the formula is simplified
-- The clausification procedure updates the state
clausifyForm ::  Form Name -> State ClausState ()
-- any formula

clausifyForm  TRUE   =
  do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> clausifyForm TRUE " ) 
    return ()   -- do nothing 

clausifyForm  FALSE  =
  do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> clausifyForm FALSE " ) 
    addClGClause []   


clausifyForm   (Atom a) =
   do
    cSt <- get 
    when (clausDebug cSt) $
      traceM ( ">>> clausifyForm (Atom a)\nARG\t" ++ show (Atom a) ) 
    addClGClause [At a] 


clausifyForm   (f1 :&: f2)  = 
   do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> clausifyForm (f1 :&: f2)\nARG\t" ++ show (f1 :&: f2) ) 
    clausifyForm f1 >> clausifyForm f2
  

clausifyForm   (f1 :|: f2)   =
   do
    cSt <- get 
    when (clausDebug cSt) $
      traceM ( ">>> clausifyForm (f1 :|: f2)\nARG\t" ++ show (f1 :|: f2) ) 
    clausifyOrLit  [] [f1,f2]

clausifyForm  ( f :=>: (g1 :&: g2) ) =
   do
    cSt <- get 
    when (clausDebug cSt) $
      traceM ( ">>> clausifyForm (f :=>: (g1 :&: g2))\nARG\t" ++ show (f :=>: (g1 :&: g2)) ) 
    clausifyForm   ( f :=>: g1 )
    clausifyForm   ( f :=>: g2 )


clausifyForm  ( (f1 :|: f2) :=>: g ) =
   do
    cSt <- get 
    when (clausDebug cSt) $
      traceM ( ">>> clausifyForm ((f :|: f2) :=>: g)\nARG\t" ++ show ( (f1 :|: f2) :=>: g ) ) 
    clausifyForm   ( f1 :=>: g )
    clausifyForm   ( f2 :=>: g )



clausifyForm   ( f :=>: (g1 :=>: g2) ) =
   do
    cSt <- get 
    when (clausDebug cSt) $
      traceM ( ">>> clausifyForm (f :=>: (g1 :=>: g2))\nARG\t" ++ show (f :=>: (g1 :=>: g2)) )
    clausifyForm   ( (f :&: g1) :=>: g2) 



clausifyForm   ( (f1 :=>: f2)  :=>: f3 ) | ( f2 /= FALSE ) &&  ( f3 /= FALSE ) =
  do
    cSt <- get
    p1 <- nameEquivWith f1
    p2 <- nameEquivWith f2
    p3 <- nameEquivWith f3
    ( when (clausDebug cSt) $
            do
              let msg = ">>> clausifyForm ((f1 :=>: f2) :=> f3), f2 /= FALSE; f3 /= FALSE\nARG\t" ++ show ((f1 :=>: f2) :=>: f3)
                        ++ "\n\tp1 = nameEquivWith f1 ---> " ++ show p1
                        ++ "\n\tp2 = nameEquivWith f2 ---> " ++ show p2
                        ++ "\n\tp3 = nameEquivWith f2 ---> " ++ show p3     
              traceM msg
      ) -- end when
    -- add:  (p1 => p2 ) => p3  
    --       p3 v (p1 -/-> p2) 
    addIntGClause [ At p3, p1 :-/->: p2 ]
    --  ** add p2 => p2
    --         ~p2 v p3
    addClGClauses [ [ Not p2, At p3] ] 

clausifyForm   (f1 :=>: f2)  =
  do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> clausifyForm (f1 :=>: f2)\nARG\t" ++ show (f1 :=>: f2) )
    clausifyImplLit    [] [f1] [f2] 


clausifyForm  (f1 :<=>: f2) =
-- f1 /= FALSE, f1 /= TRUE,  f2 /= FALSE, f2 /= TRUE
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
    -- add p1 <=> p2
    --     ~p1 v p2, ~p2 v p1
    addClGClauses [ [Not p1, At p2] , [Not p2, At p1]  ] 




clausifyOrLit ::  [GenLit Name] -> [Form Name] -> State ClausState ()
-- clausifyOr [x1 .. xm] [f1 ... fn]  (with x1 ... xm general literals, f1 .. fn any formulas)
-- clausify  the formula
--   x1 v ...v xm v f1 v...  v fn

clausifOrLit   [] [] = return () 
clausifyOrLit  xs [] = addGClause  xs

clausifyOrLit  xs (TRUE : fs)  =  clausifyOrLit   [] []

clausifyOrLit   xs (FALSE : fs)  =  clausifyOrLit   xs fs

clausifyOrLit   xs ((f1 :|: f2) : fs) =  clausifyOrLit   xs (f1 : f2 : fs)


clausifyOrLit   xs (f1 : fs) =  
  do
    cst <- get
    p1 <-
      case  clausType cst of
        WeakClausification    -> nameThatImplies f1
        StrongClausification  -> nameEquivWith   f1
    clausifyOrLit   (At p1 : xs) fs



clausifyImplLit ::  [GenLit Name] -> [Form Name] -> [Form Name] ->  State ClausState ()
-- clausifyImplLit [At a, ... Not b, ... c -/-> d, ... ] [f, ...]  [g, ...]
--   with f, ... , g, ... any formulas
-- clausify  the formula
-- (b &  .. & c -/->d &  ... & f & ...  ) -> ( a v ...v g v ...)

clausifyImplLit   [] [] [] = return ()
clausifyImplLit   xs [] [] = addGClause  xs

clausifyImplLit   xs fs  ( TRUE : gs ) = return ()
clausifyImplLit   xs fs  ( FALSE : gs ) = clausifyImplLit  xs fs gs
clausifyImplLit   xs fs  ( Atom a : gs ) = clausifyImplLit   (At a : xs) fs gs
clausifyImplLit   xs fs ( ( g1 :|: g2 ) : gs) =  clausifyImplLit   xs fs ( g1 : g2 : gs)

clausifyImplLit    xs fs (g : gs) =  
   do
    cst <- get
    p <-
      case  clausType cst of
        WeakClausification    -> nameThatImplies g
        StrongClausification  -> nameEquivWith   g
    clausifyImplLit (At p : xs) fs gs 

--  gs empty

clausifyImplLit   xs ( TRUE : fs) []  = clausifyImplLit   xs fs []
clausifyImplLit   xs ( FALSE : fs) []  = return ()

clausifyImplLit   xs ( Atom a : fs) [] = clausifyImplLit   (Not a : xs) fs []
clausifyImplLit   xs ( (f1 :&: f2) : fs) [] = clausifyImplLit   xs (f1 : f2 : fs) []

clausifyImplLit   xs ( (Atom a :=>: FALSE) : fs) [] =
  clausifyImplLit ( (a :-/->: false) : xs) fs []

clausifyImplLit   xs ( (Atom a :=>: Atom b) : fs) [] = clausifyImplLit    ( (a :-/->: b) : xs) fs []

clausifyImplLit   xs ( ((f1 :|: f2) :=>: f3) : fs) [] =  clausifyImplLit    xs ( (f1  :=>: f3) :  (f2  :=>: f3) : fs) []  
clausifyImplLit   xs ( (f1 :=>: (f2 :&: f3)) : fs) [] =  clausifyImplLit    xs ( (f1  :=>: f2) :  (f1  :=>: f3) : fs) [] 


clausifyImplLit   xs (f : fs) [] =  
   do
    cSt <- get 
    p <-
      case  clausType cSt of
        WeakClausification    -> nameImpliedBy f
        StrongClausification  -> nameEquivWith f
    ( when (clausDebug cSt) $
            do
              let msg = ">>> clausifyImplLit xs (f : fs) []"
                        ++ "\n\tp1 = f ---> " ++ show f
                        ++ "\n\tp1 = nameEquivWith f ---> " ++ show p
              traceM msg
      ) -- end when
    clausifyImplLit   (Not p : xs) fs []


