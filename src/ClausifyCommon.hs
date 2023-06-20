{-# LANGUAGE TypeOperators #-}


module ClausifyCommon

 where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Control.Monad.State
import Debug.Trace

import Language


data ClausState =
  ClaussState{
    clausType ::  ClausificationType , -- type of clausification 
    clausCache_simpleForm_name  :: Map.Map SimpleForm  Name ,            --  map  simpleForm  |---> name (local cache) 
    clausIndex :: Int,    -- index of the next new name
    clausClGCset ::  Set.Set (GenClause Name),      --  clauses         created during clausification
    clausIntGCset :: Set.Set (GenClause Name), --  impl. clauese    created during clausification
    clausCountReducedIGCs :: Int,  -- count the number of reduced IGC (used only in ClaessenRosen clausification)
    clausDebug :: Bool  -- True to debug 
    }         

mkClausState ::  ClausificationType -> Bool -> Int -> ClausState
-- index: index of the next new name
mkClausState cType debug index =
  ClaussState{
    clausType =  cType,
    clausCache_simpleForm_name  = Map.empty,
    clausIndex = index,
    clausClGCset = Set.empty,
    clausIntGCset = Set.empty,
    clausCountReducedIGCs = 0,
    clausDebug = debug
    }     

-- mkNewName :: Int -> Name
-- make the name of a new atom,  having form "$pk", with k >= 0
mkNewName :: Int -> Name
mkNewName k =  "$p" ++ show k


--------------------------------------------------------------------------------
-- simplify:
-- 1) logical constants TRUE and FALSE
-- 2) equal subformulas (e.g., f & f |---> f )
simplify :: Form Name -> Form Name

simplify (f1 :&: f2) = simplify f1 .&. simplify f2
 where
  f1     .&. f2 | f1 == f2 = f1
  TRUE   .&. f2      = f2
  f1     .&. TRUE    = f1
  FALSE  .&. f2      = FALSE
  f1     .&. FALSE   = FALSE
  f1     .&. f2      = f1 :&: f2

simplify (f1 :|: f2) = simplify f1 .|. simplify f2
 where
  f1 .|. f2 | (f1 == f2) = f1
  TRUE   .|. f2     = TRUE
  f1     .|. TRUE   = TRUE
  FALSE  .|. f2     = f2
  f1     .|. FALSE  = f1
  f1     .|. f2     = f1 :|: f2

simplify (f1 :=>: f2) = simplify f1 .=>. simplify f2
 where
  f1 .=>. f2 | (f1 == f2) = TRUE
  TRUE    .=>. f2     = f2
  f1      .=>. TRUE   = TRUE
  FALSE   .=>. f2     = TRUE
  f1      .=>. f2     = f1 :=>: f2

simplify (f1 :<=>: f2) = simplify f1 .<=>. simplify f2
 where
  f1 .<=>. f2 | (f1 == f2) = TRUE
  TRUE   .<=>. f2     = f2
  f1     .<=>. TRUE   = f1
  FALSE  .<=>. f2     = f2 :=>: FALSE
  f1     .<=>. FALSE  = f1 :=>: FALSE
  f1     .<=>. f2     = f1 :<=>: f2

simplify f = f

{-
 simple form ::= (p1 & p2)  ||  (p1 | p2)  ||  (p1 => p2) || (p1 <=> p2 )
                  p1, p2 atoms

Let simpleF be a simple form.
We write

  simpleF |---> p

to mean that p is a name denoting simpleF.

If simpleF is a propositional formula, then  we set p = simpleF


-}


{-

We usa the notation

   f1 |-- f2

to mean that f2 is classical provable from the clauses stored  in the current clause state.


-}
  

nameThatImplies :: Form Name -> State ClausState Name
-- return a name p which implies f, namely  p |-- f, possibly updating the state


nameThatImplies  (Atom a) =
  do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> nameThatImplies (Atom a)\nARG\t" ++ show (Atom a) ) 
    return a

nameThatImplies  (f1 :&: f2) = 
{- 
Asssume

 p1 |-- f1
 p2 |-- f2     

We have

 p1 & p2  |-- f1 & f2

Let

 p1 & p2 |---> q

We add

    q => p1
    q => p2

and we get

   q |-- f1 & f2

-}
 do
    cSt <- get
    p1 <- nameThatImplies f1
    p2 <- nameThatImplies f2
    q  <- nameOf_simpleForm  (p1 :&&: p2)
    ( when (clausDebug cSt) $
            do
              let msg = ">>> nameThatImplies (f1 :&: f2)\nARG\t" ++ show (f1 :&: f2)
                    ++  "\n\tp1 = nameThatImplies f1 ---> " ++ show p1 
                    ++  "\n\tp2 = nameThatImplies f2 ---> " ++ show p2 
                    ++  "\nRESULT\tnameOf_simpleForm (p1 :&&: p2) ---> " ++ show q 
              traceM msg
      ) -- end when
    -- add   q => p1 , q => p2 
    --       ~q v p1 , ~q v p2
    addClGClauses [
         [ Not q, At p1] ,
         [ Not q, At p2]
       ]   
    return q


nameThatImplies (f1 :|: f2) =
{- 
Asssume

 p1 |-- f1
 p2 |-- f2     

We have

 p1 v p2  |-- f1 v f2

Let

 p1 v p2 |---> q

We add

   q => p1 v p2 

and we get

   q |-- f1 v f2 

-}
  do
    cSt <- get 
    p1 <- nameThatImplies f1
    p2 <- nameThatImplies f2
    q  <- nameOf_simpleForm  (p1 :||: p2)
    ( when (clausDebug cSt) $
            do
              let msg = ">>> nameThatImplies (f1 :|: f2)\nARG\t" ++ show (f1 :|: f2) 
                   ++   "\n\tp1 = nameThatImplies f1 ---> " ++ show p1 
                    ++  "\n\tp2 = nameThatImplies f2 ---> " ++ show p2 
                    ++  "\nRESULT\tnameOf_simpleForm (p1 :||: p2) ---> " ++ show q 
              traceM msg
      ) -- end when
    -- add  q => p1 v p2 
    --      ~q v p1 v p2 
    addClGClauses [
     [ Not q, At p1, At p2] 
      ] 
    return q


nameThatImplies (f1 :=>: FALSE) =
{- 
f1 /= FALSE

Asssume

 f1 |-- p1 

We have

 p1 => FALSE |--  f1 => FALSE

Let

 p1 => FALSE |---> q

We add

   q & p1 => FALSE  

and we get

   q |-- f1 => FALSE 

-}
  do
    cSt <- get
    p1 <- nameImpliedBy f1
    q  <- nameOf_simpleForm  (p1 :==>: false)
    ( when (clausDebug cSt) $
            do
              let msg = ">>> nameThatImplies (f1 :=>: FALSE)\nARG\t" ++ show (f1 :=>: FALSE)
                    ++  "\n\tp1 = nameImpliedBy f1 ---> " ++ show p1 
                    ++  "\nRESULT\tnameOf_simpleForm (p1 :==>: false) ---> " ++ show q 
              traceM msg
      ) -- end when
    -- add   q & p1 =>  FALSE    
    --       ~q v ~p1    
    addClGClauses [ [Not q, Not p1] ]
    return q


nameThatImplies  (f1 :=>: f2) =
{- 
f1 /= FALSE, f2 /= FALSE

Asssume

 f1 |-- p1
 p2 |-- f2      

We have

 p1 => p2 |-- f1 => f2

Let

 p1 => p2 |---> q

We add

   q & p1 =>  p2   

and we get

   q |-- f1 => f2 

-}

  do
    cSt <- get
    p1 <- nameImpliedBy f1
    p2 <- nameThatImplies f2
    q  <- nameOf_simpleForm  (p1 :==>: p2)
    ( when (clausDebug cSt) $
            do
              let msg = ">>> nameThatImplies (f1 :=>: f2)\nARG\t" ++ show (f1 :=>: f2) 
                    ++  "\n\tp1 = nameImpliedBy f1  ---> " ++ show p1 
                    ++  "\n\tp2 = nameThatImplies f2 ---> " ++ show p2 
                    ++  "\nRESULT\tnameOf_simpleForm (p1 :==>: p2) ---> " ++ show q 
              traceM msg
      ) -- end when
    -- add  q & p1 =>  p2    
    --      ~q v ~p1 v p2   
    addClGClauses [ [ Not q, Not p1, At p2] ]
    return q


-- for formula f1 :<=>: f2 we have to proceed according to  the clausification type
nameThatImplies (f1 :<=>: f2) =
  do
    cSt <- get
    if ( isGeneralClausesClausificationType . clausType ) cSt
      then nameThatImplies_genC       (f1 :<=>: f2)
      else nameThatImplies_claessenR  (f1 :<=>: f2)    

nameThatImplies_genC :: Form Name -> State ClausState Name
nameThatImplies_genC (f1 :<=>: f2)  =
{- 
f1 /= FALSE, f2 /= FALSE

Assume

  |--  p1 <=> f1  
  |--  p2 <=> f2   

We have

  p1 <=> p2 |-- f1 <=> f2

Let

 p1 => p2 |---> q1
 p2 => p1 |---> q2
  q1 & q2 |---> q

We add

   q => q1
   q => q2
   q1 & p1 =>  p2
   q2 & p2 =>  p1

which implies

   q |-- p1 <=> p2

We get

   q |-- f1 <=> f2 


-}
  do
    cSt <- get
    p1 <- nameEquivWith f1
    p2 <- nameEquivWith f2
    q1 <- nameOf_simpleForm (p1 :==>: p2)
    q2 <- nameOf_simpleForm (p2 :==>: p1)
    q  <- nameOf_simpleForm (q1 :&&: p2)
    ( when (clausDebug cSt) $
            do
              let msg = ">>> nameThatImplies (f1 :<=>: f2)\nARG\t" ++ show (f1 :<=>: f2) 
                     ++ "\n\tp1 = nameEquivWith f1 ---> " ++ show p1 
                     ++ "\n\tp2 = nameEquivWith f2 ---> " ++ show p2
                     ++ "\n\tq1 = nameOf_simpleForm (p1 :==>: p2) ---> " ++ show q1
                     ++ "\n\tq2 = nameOf_simpleForm (p2 :==>: p1) ---> " ++ show q2 
                     ++ "\nRESULT\tnameOf_simpleForm (q1 :&&: q2) ---> " ++ show q 
              traceM msg
      ) -- end when
    --  add q => p1 , q =>  p2 , q1 & p1 =>  p2 , q2 & p2 =>  p1 
    --      ~q v p1 , ~q v p2  , ~q1 v ~p1 v p2 , ~q2 v ~p2 v p1
    addClGClauses[
        [ Not q,  At p1 ],
        [ Not q,  At p2 ],
        [ Not q1,  Not p1, At p2 ],
        [ Not q2,  Not p2, At p1 ]
      ]  
    return q

nameThatImplies_claessenR :: Form Name -> State ClausState Name
nameThatImplies_claessenR (f1 :<=>: f2) =
{- 
f1 /= FALSE, f2 /= FALSE

Asssume
 |-- p1 <=> f1 
 |-- p2 <=> f2      

We have

 p1 <=> p2 |-- f1 <=> f2

Let

 p1 <=> p2 |---> q

We add

   q & p1 =>  p2
   q & p2 =>  p1

which implies

   q |-- p1 <=> p2)

We get

   q |-- f1 <=> f2 


-}
  do
    cSt <- get
    p1 <- nameEquivWith f1
    p2 <- nameEquivWith f2
    q  <- nameOf_simpleForm (p1 :<==>: p2)
    ( when (clausDebug cSt) $
            do
              let msg = ">>> nameThatImplies (f1 :<=>: f2)\nARG\t" ++ show (f1 :<=>: f2) 
                      ++ "\n\tp1 = nameEquivWith f1 ---> " ++ show p1 
                      ++ "\n\tp2 = nameEquivWith f2 ---> " ++ show p2 
                      ++ "\nRESULT\tnameOf_simpleForm (p1 :<==>: p2) ---> " ++ show q 
              traceM msg
      ) -- end when
    --  add  q & p1 =>  p2 , q & p2 =>  p1 
    --       ~q v ~p1 v p2 , ~q v ~p2 v p1 
    addClGClauses[
        [ Not q,  Not p1, At p2 ],
        [ Not q,  Not p2, At p1 ]
      ]  
    return q


nameImpliedBy :: Form Name -> State ClausState Name
-- return a name p implied by f, namely f |-- p, possibly updating the state

nameImpliedBy  (Atom a) =
  do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> nameImpliedBy (Atom a)\nARG\t" ++ show (Atom a) ) 
    return a

nameImpliedBy (f1 :&: f2) =
{- 
Asssume

 f1 |-- p1
 f2 |-- p2     

We have

 f1 & f2 |-- p1 & p2

Let

 p1 & p2 |---> q

We add

    p1 & p2 => q

and we get

   f1 & f2 |-- q

-}
  do
    cSt <- get
    p1 <- nameImpliedBy f1
    p2 <- nameImpliedBy f2
    q  <- nameOf_simpleForm  (p1 :&&: p2)
    ( when (clausDebug cSt) $
            do
              let msg =  ">>> nameImpliedBy (f1 :&: f2)\nARG\t" ++ show (f1 :&: f2) 
                      ++ "\n\tp1 = nameImpliedBy f1 ---> " ++ show p1 
                      ++ "\n\tp2 = nameImpliedBy f2 ---> " ++ show p2 
                      ++ "\nRESULT\tnameOf_simpleForm (p1 :&&: p2) ---> " ++ show q 
              traceM msg
      ) -- end when
    -- add   p1 & p2 => q
    --       ~p1 v ~p2 v q
    addClGClauses [ [ Not p1, Not p2, At q] ]   
    return q

nameImpliedBy (f1 :|: f2) =
{- 
Asssume

 f1 |-- p1
 f2 |-- p2     

We have

 f1 v f2 |-- p1 v p2

Let

 p1 v p2 |---> q

We add

   p1  => q
   p2 => q

and we get

   f1 v f2 |-- q

-}
  do
    cSt <- get
    p1 <- nameImpliedBy  f1
    p2 <- nameImpliedBy  f2
    q  <- nameOf_simpleForm  (p1 :||: p2)
    ( when (clausDebug cSt) $
            do
              let msg = ">>> nameImpliedBy (f1 :|: f2)\nARG\t" ++ show (f1 :|: f2) 
                     ++ "\n\tnameImpliedBy f1 ---> " ++ show p1 
                     ++ "\n\tnameImpliedBy f2 ---> " ++ show p2 
                     ++ "\nRESULT\tnameOf_simpleForm (p1 :||: p2) ---> " ++ show q 
              traceM msg
      ) -- end when
    -- add  p1  => q ,  p2 => q
    --      ~p1 v q  ,  ~p2 v q
    addClGClauses [
      [ Not p1, At q] ,
      [ Not p2, At q]
     ] 
    return q


nameImpliedBy (f1 :=>: FALSE) =
{- 
f1 /= FALSE

Asssume

 p1 |-- f1 

We have

 f1 => FALSE  |-- p1 => FALSE

Let

 p1 => FALSE |---> q

We add

    (p1  => FALSE) => q

and we get

    f1 => FALSE |-- q

-}
  do
    cSt <- get
    p1 <- nameThatImplies  f1
    q  <- nameOf_simpleForm  (p1 :==>: false)
    ( when (clausDebug cSt) $
            do
              let msg =  ">>> nameImpliedBy (f1 :=>: FALSE)\nARG\t" ++ show (f1 :=>: FALSE) 
                      ++ "\n\tp1 = nameImpliedBy f1 ---> " ++ show p1 
                      ++ "\nRESULT\tnameOf_simpleForm (p1 :==>: false) ---> " ++ show q 
              traceM msg
      ) -- end when
    -- add   (p1 => FALSE ) => q  
    --       q v (p1 -/-> FALSE) 
    addIntGClause [ At q, p1 :-/->: false ]
    return q

  
nameImpliedBy  (f1 :=>: f2) =
{- 
f1 /= FALSE, f2 /= FALSE

Asssume

 p1 |-- f1
 f2 |-- p2      

We have

 f1 => f2  |-- p1 => p2

Let

 p1 => p2 |---> q

We add

     (p1  => p2) => q

and we get

   f1 => f2 |-- q

** We also add

  p2 => q

-}
  do
    cSt <- get
    p1 <- nameThatImplies  f1
    p2 <- nameImpliedBy    f2
    q  <- nameOf_simpleForm  (p1 :==>: p2)
    ( when (clausDebug cSt) $
            do
              let msg = ">>> nameImpliedBy (f1 :=>: f2)\nARG\t" ++ show (f1 :=>: f2) 
                     ++ "\n\tp1 = nameThatImplies f1  ---> " ++ show p1 
                     ++ "\n\tp2 = nameImpliedBy f2 ---> " ++ show p2 
                     ++ "\nRESULT\tnameOf_simpleForm (p1 :==>: p2) ---> " ++ show q 
              traceM msg
      ) -- end when
    -- add  (p1 => p2) => q  
    --      q v (p1 -/-> p2) 
    addIntGClause [ At q, p1 :-/->: p2 ]
    -- ** add  p2 => q
    --         ~p2 v q
    addClGClauses [ [ Not p2, At q] ] 
    return q
  
-- for formula f1 :<=>: f2 we have to proceed according to  the clausification type
nameImpliedBy (f1 :<=>: f2) =
  do
    cSt <- get
    if ( isGeneralClausesClausificationType . clausType ) cSt
      then nameImpliedBy_genC       (f1 :<=>: f2)
      else nameImpliedBy_claessenR  (f1 :<=>: f2)   

nameImpliedBy_genC :: Form Name -> State ClausState Name
nameImpliedBy_genC   (f1 :<=>: f2)   =
{- 
f1 /= FALSE, f2 /= FALSE

Asssume

 |-- p1 <=> f1
 |-- p2 <=> f2      

We have

 f1 <=> f2 |-- p1 <=> p2

Let

 p1 => p2 |---> q1
 p2 => p1 |---> q2
  q1 & q2 |---> q

We add

     (p1 => p2) => q1
     (p2 => p1) => q2
     q1 & q2 => q

which implies

   p1 <=> p2 |-- q

We get

   f1 <=> f2 |-- q

** We also add

  p2 => q1 , p1 => q2

-}
  do
    cSt <- get
    p1 <- nameEquivWith f1
    p2 <- nameEquivWith f2
    q1 <- nameOf_simpleForm (p1 :==>: p2)
    q2 <- nameOf_simpleForm (p2 :==>: p1)
    q  <- nameOf_simpleForm (q1 :&&: p2)
    ( when (clausDebug cSt) $
            do
              let msg = ">>> nameImpliedBy (f1 :<=>: f2)\nARG\t" ++ show (f1 :<=>: f2) 
                    ++ "\n\tp1 = nameEquivWith f1 ---> " ++ show p1 
                    ++ "\n\tp2 = nameEquivWith f2 ---> " ++ show p2
                    ++ "\n\tq1 = nameOf_simpleForm (p1 :==>: p2) ---> " ++ show q1
                    ++ "\n\tq2 = nameOf_simpleForm (p2 :==>: p1) ---> " ++ show q2 
                    ++ "\nRESULT\tnameOf_simpleForm (q1 :&&: q2) ---> " ++ show q 
              traceM msg
      ) -- end when
   --  add  (p1 => p2) => q1  , (p2 => p1) => q2 ,  q1 & q2 => q
   --       q1 v (p1 -/-> p2) , q2 v (p2 -/-> p1) , ~q1 v ~q2 v q
    
    addIntGClauses [
       [ At q1, p1 :-/->: p2 ] ,
       [ At q2, p2 :-/->: p1]
      ]
    addClGClauses[
        [ Not q1, Not q2, At q ]
       ]
    --  ** add   p2 => q1 , p1 => q2
    --           ~p2 v q1 , ~p1 v q2    
    addClGClauses[
        [ Not p2, At q1] ,
        [ Not p1, At q2] 
      ]
    return q

nameImpliedBy_claessenR :: Form Name -> State ClausState Name
nameImpliedBy_claessenR  (f1 :<=>: f2)  =
{- 
f1 /= FALSE, f2 /= FALSE

Asssume

 |-- p1 <=> f1
 |-- p2 <=> f2      

We have

 f1 <=> f2  |-- p1 <=> p2

Let

  p1 => p2  |---> q1
  p2 => p1  |---> q2
  p1 <=> p2 |---> q

We add

     (p1 => p2) => q1
     (p2 => p1) => q2
     q1 & q2 => q

Note that

     p1 <=> p2 |-- q

We get

  f1 <=> f2 |-- q

** We also add

  p2 => q1 , p1 => q2

-}
  do
    cSt <- get
    p1 <- nameEquivWith f1
    p2 <- nameEquivWith f2
    q1 <- nameOf_simpleForm (p1 :==>: p2)
    q2 <- nameOf_simpleForm (p2 :==>: p1)
    q  <- nameOf_simpleForm (q1 :<==>: p2)
    ( when (clausDebug cSt) $
            do
              let msg = ">>> nameImpliedBy (f1 :<=>: f2)\nARG\t" ++ show (f1 :<=>: f2) 
                    ++ "\n\tp1 = nameEquivWith f1 ---> " ++ show p1 
                    ++ "\n\tp2 = nameEquivWith f2 ---> " ++ show p2 
                    ++ "\n\tq1 = nameOf_simpleForm (p1 :==>: p2)  ---> " ++ show q1 
                    ++ "\n\tq2 = nameOf_simpleForm (p2 :==>: p1) ---> " ++ show q2 
                    ++ "\nRESULT\tnameOf_simpleForm (p1 :<==>: p2) ---> " ++ show q 
              traceM msg
      ) -- end when
   --  add  (p1 => p2) => q1  , (p2 => p1) => q2 ,  q1 & q2 => q
   --       q1 v (p1 -/-> p2) , q2 v (p2 -/-> p1) , ~q1 v ~q2 v q
    addIntGClauses [
       [ At q1, p1 :-/->: p2 ] ,
       [ At q2, p2 :-/->: p1]
      ]
    addClGClauses[
        [ Not q1, Not q2, At q ]
       ]
    --  ** add   p2 => q1 , p1 => q2
    --           ~p2 v q1 , ~p1 v q2    
    addClGClauses[
        [ Not p2, At q1] ,
        [ Not p1, At q2] 
      ]
    return q




nameEquivWith :: Form Name -> State ClausState Name
-- return a name p equivalent with f,  namely |-- p <=> f, possibly updating the state
nameEquivWith  (Atom a) =
  do
    cSt <- get
    when (clausDebug cSt) $
      traceM ( ">>> nameEquivWith (Atom a)\nARG\t" ++ show (Atom a) ) 
    return a


nameEquivWith  (f1 :&: f2) =
{-
Asssume

 |-- p1 <=> f1
 |-- p2 <=> f2     

We have

 |-- p1 & p2  <=> f1 & f2

Let

 p1 & p2 |---> q

We add

   q => p1
   q => p2
   p1 & p2 => q

which implies
  
  |--  q <=> p1 & p2 

We get

  |-- f1 & f2 <=> q

-}
  do
    cSt <- get
    p1 <- nameEquivWith  f1
    p2 <- nameEquivWith  f2
    q  <- nameOf_simpleForm  (p1 :&&: p2)
    ( when (clausDebug cSt) $
            do
              let msg = ">>> nameEquivWith (f1 :&: f2)\nARG\t" ++ show (f1 :&: f2) 
                     ++ "\n\tp1 = nameEquivWith f1 ---> " ++ show p1 
                     ++ "\n\tp2 = nameEquivWith f2 ---> " ++ show p2 
                     ++ "\nRESULT\tnameOf_simpleForm (p1 :&&: p2) ---> " ++ show q 
              traceM msg
      ) -- end when
    -- add   q => p1 , q => p2 , p1 & p2 => q
    --       ~q v p1 , ~q v p2 , ~p1 v ~p2 v q
    addClGClauses [
      [ Not q, At p1] ,
      [ Not q, At p2],
      [ Not p1, Not p2, At q]
      ]   
    return q

nameEquivWith (f1 :|: f2) =
{- 
Asssume

 |-- p1 <=> f1
 |-- p2 <=> f2     

We have

 |-- p1 v p2  <=> f1 v f2

Let

 p1 v p2 |---> q

We add

    q => p1 v p2
    p1 => q
    p2 => q

which implies
  
  |-- q <=> p1 v p2 

We get

   |-- q <=> f1 v f2 

-}
  do
    cSt <- get
    p1 <- nameEquivWith  f1
    p2 <- nameEquivWith  f2
    q  <- nameOf_simpleForm  (p1 :||: p2)
    ( when (clausDebug cSt) $
            do
              let msg = ">>> nameEquivWith (f1 :|: f2)\nARG\t" ++ show (f1 :|: f2) 
                    ++ "\n\tp1 = nameEquivWith f1 ---> " ++ show p1 
                    ++ "\n\tp2 = nameEquivWith f2 ---> " ++ show p2 
                    ++ "\nRESULT\tnameOf_simpleForm (p1 :||: p2) ---> " ++ show q 
              traceM msg
      ) -- end when
    -- add  q => p1 v p2 ,  p1  => q ,  p2 => q
    --      ~q v p1 v p2 ,  ~p1 v q  ,  ~p2 v q
    addClGClauses [
      [ Not q, At p1, At p2] ,
      [ Not p1, At q] ,
      [ Not p2, At q]
      ] 
    return q


nameEquivWith  (f1 :=>: FALSE) =
{- 
f1 /= FALSE

Asssume

 |-- p1 <=> f1 

We have

 |--  (p1 => FALSE) <=>  (f1 => FALSE)  

Let

 p1 => FALSE |---> q

We add

   (p1 => FALSE) => q
   q & p1 => FALSE  

which implies

  |-- q <=> (p1 => FALSE ) 

We get

  |-- q <=> (f1 => FALSE) 

-}
  do
    cSt <- get
    p1 <- nameEquivWith  f1
    q  <- nameOf_simpleForm  (p1 :==>: false)
    ( when (clausDebug cSt) $
            do
              let msg = ">>> nameEquivWith (f1 :=: FALSE)\nARG\t" ++ show (f1 :=>: FALSE) 
                      ++ "\n\tp1 = nameEquivWith f1 ---> " ++ show p1 
                      ++ "\nRESULT\tnameOf_simpleForm (p1 :==>: false) ---> " ++ show q 
              traceM msg
      ) -- end when
    -- add   (p1 => FALSE ) => q  ,    q & p1 =>  FALSE    
    --       q v (p1 -/-> false) ,     ~q v ~p1    
    addIntGClause [ At q, p1 :-/->: false ]
    addClGClauses [ [Not q, Not p1] ]
    return q


nameEquivWith  (f1 :=>: f2) =
  {- 
f1 /= FALSE, f2 /= FALSE

Asssume

 |-- f1 <=> p1
 |-- f2 <=> p2      

We have

 |-- (f1 => f2)  <=> (p1 => p2)

Let

 p1 => p2 |---> q

We add

   (p1 => p2) => q
   q & p1 =>  p2   

which implies

  |-- (p1  => p2) <=> q

We get

  |-- (f1 => f2) <=> q

** We also add   

  p2 => q


-}
 do
    cSt <- get
    p1 <- nameEquivWith  f1
    p2 <- nameEquivWith  f2
    q  <- nameOf_simpleForm  (p1 :==>: p2)
    ( when (clausDebug cSt) $
            do
              let msg = ">>> nameEquivWith (f1 :=>: f2)\nARG\t" ++ show (f1 :=>: f2) 
                    ++ "\n\tp1 = nameEquivWith f1 ---> " ++ show p1 
                    ++ "\n\tp2 = nameEquivWith f2 ---> " ++ show p2 
                    ++ "\nRESULT\tnameOf_simpleForm (p1 :==>: p2) ---> " ++ show q 
              traceM msg
      ) -- end when
    -- add:  (p1 => p2) => q  , p2 => q ,   q & p1 =>  p2    
    --       q v (p1 -/-> p2) , ~p2 v q ,   ~q v ~p1 v p2   
    addIntGClause [ At q, p1 :-/->: p2 ]
    addClGClauses [
       [ Not p2, At q] ,
       [ Not q, Not p1, At p2]
       ]
    return q

-- for formula f1 :<=>: f2 we have to proceed according to  the clausification type
nameEquivWith (f1 :<=>: f2) =
  do
    cSt <- get
    if ( isGeneralClausesClausificationType . clausType ) cSt
      then nameEquivWith_genC       (f1 :<=>: f2)
      else nameEquivWith_claessenR  (f1 :<=>: f2)    

nameEquivWith_genC :: Form Name -> State ClausState Name
nameEquivWith_genC  (f1 :<=>: f2) =
{- 
f1 /= FALSE, f2 /= FALSE

Asssume

 |-- p1 <=> f1
 |-- p2 <=> f2      

We have

 |--  (p1 <=> p2)  <=> (f1 <=> f2)

Let

 p1 <=> p2  |---> q
  p1 => p2  |---> q1
  p2 => p1  |---> q2
       
 We add
 
     q & p1 => p2
     q & p2 => p1
    q1 & p1 => p2
    q2 & p2 => p1
    q1 & q2 => q
 (p1 => p2) => q1
 (p2 => p1) => q2  

which implies

 |--  q <=> (p1 <=> p2)

We get

 |--  q <=> (f1 <=> f2) 


** We also add

 p2 => q1 , p1 => q2  

-}
  do
    cSt <- get
    p1 <- nameEquivWith f1
    p2 <- nameEquivWith f2
    q1 <- nameOf_simpleForm (p1 :==>: p2)
    q2 <- nameOf_simpleForm (p2 :==>: p1)
    q  <- nameOf_simpleForm (p1 :<==>: p2)
    ( when (clausDebug cSt) $
            do
              let msg = ">>> nameEquivWith (f1 :<=>: f2)\nARG\t" ++ show (f1 :<=>: f2) 
                    ++ "\n\tp1 = nameEquivWith f1 ---> " ++ show p1 
                    ++ "\n\tp2 = nameEquivWith f2 ---> " ++ show p2
                    ++ "\n\tq1 = nameOf_simpleForm (p1 :==>: p2) ---> " ++ show q1
                    ++ "\n\tq2 = nameOf_simpleForm (p2 :==>: p1) ---> " ++ show q2 
                    ++ "\nRESULT\tnameOf_simpleForm (p1 :<=>: p2) ---> " ++ show q 
              traceM msg
      ) -- end when
    --  add  q & p1 => p2 , q & p2 => p1  , q1 & p1 => p2  , q2 & p2 => p1  , q1 & q2 => q
    --      ~q v ~p1 v p2 , ~q v ~p2 v p1 , ~q1 v ~p1 v p2 , ~q2 v ~p2 v p1 , ~q1 v ~q2 v q 
    addClGClauses[
        [ Not q,  Not p1, At p2 ],
        [ Not q,  Not p2, At p1 ],
        [ Not q1,  Not p1, At p2 ],
        [ Not q2,  Not p2, At p1 ],
        [ Not q1,  Not q2, At q ]
      ]
    -- add (p1 => p2) => q1 , (p2 => p1) => q2  
    --       q1 v (p1 -/-> p2) , q2 v (p2 -/-> p1) 
    addIntGClauses [
       [ At q1, p1 :-/->: p2 ] ,
       [ At q2, p2 :-/->: p1]
      ]
    --  ** add  p2 => q1 , p1 => q2
    --          ~p2 v q1 , ~p1 v q2
    addClGClauses[
        [ Not p2, At q1],
        [ Not p1, At q2]
      ]
    return q



nameEquivWith_claessenR :: Form Name -> State ClausState Name
nameEquivWith_claessenR  (f1 :<=>: f2) =
{- 
f1 /= FALSE, f2 /= FALSE

Asssume

 |-- p1 <=> f1
 |-- p2 <=> f2      

We have

 |-- (p1 <=> p2)  <=> (f1 <=> f2)

Let

  p1 => p2   |---> q1
  p2 => p1   |---> q2
  p1 <=> p2  |---> q

We add:

 q & p1 =>  p2
 q & p2 =>  p1
 (p1 => p2) => q1
 (p2 => p1) => q2  
 q1 & q2 => q

which implies

  |-- q <=> (p1 <=> p2)

We get

 |--  q <=> (f1 <=> f2) 

** We also add

 p2 => q1 , p1 => q2  

-}
  do
    cSt <- get
    p1 <- nameEquivWith f1
    p2 <- nameEquivWith f2
    q1 <- nameOf_simpleForm (p1 :==>: p2)
    q2 <- nameOf_simpleForm (p2 :==>: p1)
    q  <- nameOf_simpleForm (p1 :<==>: p2)
    ( when (clausDebug cSt) $
            do
              let msg = ">>> nameEquivWith (f1 :<=>: f2)\nARG\t" ++ show (f1 :<=>: f2) 
                    ++ "\n\tp1 = nameEquivWith f1 ---> " ++ show p1 
                    ++ "\n\tp2 = nameEquivWith f2 ---> " ++ show p2 
                    ++ "\n\tq1 = nameEquivWith p1 :==>: p2  ---> " ++ show q1 
                    ++ "\n\tq2 = nameEquivWith p2 :==>: p1  ---> " ++ show q2 
                    ++ "\nRESULT\tnameOf_simpleForm (p1 :<==>: p2) ---> " ++ show q 
              traceM msg
      ) -- end when
    --  add  q & p1 => p2 , q & p2 => p1 ,  q1 & q2 => q
    --      ~q v ~p1 v p2 , ~q v ~p2 v p1 , ~q1 v ~q2 v q 
    addClGClauses[
        [ Not q,  Not p1, At p2 ],
        [ Not q,  Not p2, At p1 ],
        [ Not q1, Not q2, At q ]
      ]
    -- add (p1 => p2) => q1  , (p2 => p1) => q2  
    --     q1 v (p1 -/-> p2) , q2 v (p2 -/-> p1) 
    addIntGClauses [
       [ At q1, p1 :-/->: p2 ] ,
       [ At q2, p2 :-/->: p1 ]
      ]
    --  ** add  p2 => q1 , p1 => q2
    --          ~p2 v q1 , ~p1 v q2
    addClGClauses[
        [ Not p2, At q1 ],
        [ Not p1, At q2 ]
      ]
    return q


normalForm :: SimpleForm -> SimpleForm
-- simple form ::= (p1 & p2)  ||  (p1 | p2)  ||  (p1 => p2) || (p1 <=> p2 )
--                  p1, p2 atoms
normalForm  (p1 :&&: p2)   | p1 > p2 = p2 :&&: p1
normalForm  (p1 :||: p2)   | p1 > p2 = p2 :||: p1
normalForm  (p1 :<==>: p2) | p1 > p2 = p2 :<==>: p1
normalForm  sf = sf


nameOf_simpleForm :: SimpleForm -> State ClausState  Name
-- return the name associated with  a simple form, by inspecting (and possibly updating) the cache
nameOf_simpleForm sf =
  do
    clausSt <- get
    let normal_sf = normalForm sf
        cache =  clausCache_simpleForm_name clausSt 
    case Map.lookup  normal_sf cache  of
       Just p -> return p
       Nothing ->
        do
          let n = clausIndex clausSt
              newName = mkNewName n
              newCache = Map.insert normal_sf newName cache 
          modify( \s ->  s{clausCache_simpleForm_name= newCache, clausIndex = n + 1 } ) 
          return newName      


addGClause :: GenClause Name -> State ClausState ()
addGClause gc | isClassicalGenClause gc = addClGClause gc
addGClause gc = addIntGClause gc -- gc is intuitionistic

addClGClause :: GenClause Name -> State ClausState ()
addClGClause [] = return ()
addClGClause gc =
  modify( \s -> s{ clausClGCset = Set.insert gc (clausClGCset s) })

addClGClauses :: [GenClause Name] -> State ClausState ()
addClGClauses = mapM_ addClGClause 
--  sequence_ [ addClGClause gc | gc <- gcs ]
  
addIntGClause :: GenClause Name -> State ClausState ()
addIntGClause gc =
  modify( \s -> s{ clausIntGCset = Set.insert gc (clausIntGCset s) } )

addIntGClauses :: [GenClause Name] -> State ClausState ()
addIntGClauses = mapM_ addIntGClause 
  -- sequence_ [ addIntGClause gc | gc <- gcs ]
