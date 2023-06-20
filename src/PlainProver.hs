{-# LANGUAGE TypeOperators #-}
module PlainProver (
    proveProblemPlain  -- Maybe Int -> GenClauseSequent Name  -> IO ()
                       -- plain prover (without trace nor countermodels/derivatons)
)
  where

-- import Data.IORef
import System.IO
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.List 
import qualified Data.PartialOrd as POrd
import System.Directory
import System.Random
import System.FilePath
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.RWS

import MiniSat  --  https://hackage.haskell.org/package/minisat

import Language
import ProverTypes
import Utility



-- ########################################################
-- #######           PROVER  PLAIN                 ########
-- ########################################################

proveProblemPlain ::  Maybe Int -> GenClauseSequent Name  -> IO ()
--- mRandomSeed: 'Just k' for  random computation with initial seed k, Nothing for non-random computation  
--  gcSeq:  problem to solve
proveProblemPlain    mRandomSeed gcSeq   = 
 do
  (proverEnv,initialProverState)  <- initProblemPlain   mRandomSeed gcSeq 
  ( res,finalProverState, _ ) <-  runRWST  proveMainPlain  proverEnv  initialProverState  
  case res of
       Valid  ->  -- valid
           putStrLn "+++ RESULT: Valid (in IPL)"
       CountSat ->
           putStrLn "+++ RESULT: CounterSatisfiable (in IPL)"

           
-- initial setup
initProblemPlain ::   Maybe Int ->  GenClauseSequent Name   ->  IO (ProverEnv,ProverState)
-- debug:  true to debug the prover
-- mRandomSeed: 'Just k' for  random computation with initial seed k, Nothing for non-random computation  
-- gcSeq:  sequent to prove
initProblemPlain   mRandomSeed gcSeq   =
 do
  let  names = getGCSeqNames gcSeq  -- all the names occurring in gcSeq
       mRandomGen0 =   mkStdGen <$>  mRandomSeed
       (names_rand,mRandomGen1)=    runState  (mShuffleSt names) mRandomGen0
  -- if we are in random mode then names_rand is a permutation of names, otherwise names_rand=names   
  sat <- newSolver
  -- create the literals (in the SAT-solver language), one for each  name occurring in the input formulas
  univ <- sequence [ newLit sat | _ <- names_rand ] -- universe  :: [Lit]
  -- create encode/decode maps 
  let nmToLt_map  = Map.fromList (names_rand `zip` univ)  -- Name to Lit map
      nmToLt =  (Map.!) nmToLt_map  -- Name -> Lit
      -- Map.! ::  Ord k => Map k a -> k -> a
      ltToNm_map = Map.fromList (univ `zip` names_rand)  -- Lit to Name map
      --  Map.lookup :: Ord k => k -> Map.Map k a -> Maybe a
  ( when  (false `elem` names)  $ -- add "not false" to the sat solver
        satAddGLit sat ( Not  (nmToLt false) )  -- false :: Name (constant)
     )
  let gcSeq_satLit  = fmap  nmToLt gcSeq
      (gcSeq_satLit_rand,mRandomGen2) = runState  (mShuffleGCSeqSt gcSeq_satLit) mRandomGen1
  -- if we are in random mode then gcSeq_satLit_rand is a permutation of  gcSeq_satLit, otherwise  gcSeq_satLit_rand= gcSeq_satLit
  satAddGClauses sat (classicalGCs gcSeq_satLit_rand)
  -- proving
  simplify sat      
  let  proverEnv = mkProverEnv ""  univ  gcSeq_satLit_rand  ltToNm_map  NoTrace False emptyCache
       initialProverState =  mkProverState sat mRandomGen2
  return  (proverEnv,initialProverState )


proveMainPlain :: ProverConf SearchResult 
proveMainPlain  =
-- main loop 
  do
    env <- ask  -- get prover environment
    pst <- get  -- get prover state
    let sat = solver pst
        gcSeq = initGCSeq env
        rightL = rightAtm gcSeq 
        mRandomGen = mRandomGenerator pst
    -- @SAT:  SAT |-- rightL ?
    isSat <- lift $ solve sat [  neg rightL ]  --  solve :: Solver -> [Lit] -> IO Bool
    if isSat then
     -- found a classical model M such M |= sat and M |=/=  rightL
     -- trueAtoms_M = atoms in M
     do
        -- ### STEP (S2) ##
         trueAtms_M <- lift $ trueAtmsInSat sat (universe env) 
         let newWorld = mkWorld 0 trueAtms_M -- all the worlds have index 0  
             newModel = addWorld newWorld emptyModel
             gcsToCheck =  [ gc | gc <- intGCs gcSeq , trueAtms_M .|=/=.  gc  ] 
             (gcsToCheck_rand,newMRandomGen) =    runState  (mShuffleSt  gcsToCheck) mRandomGen
             -- if we are in random mode then gcsToCheck_rand is a permutation of gcsToCheck, otherwise gcsToCheck_rand=gcsToCheck
             newWorldRec = mkWorldRec newWorld gcsToCheck_rand
         modify ( \ s -> s{model = newModel} )
         ( when ( isJust mRandomGen) $  -- update random generator
               modify (\s ->  s{mRandomGenerator =  newMRandomGen} )
           ) -- end when
         middleLoop [ newWorldRec ] -- start middle loop 
       else
      --  the answer is Yes({}), thus   sat |-- rightL
      --  Hence gcSeq is proved
        do 
          -- update prover state
          modify ( \ s -> s{isValidForm = True  }  )
          return  Valid    


-- Middle loop 
middleLoop :: [ WorldRec Lit ]  -> ProverConf SearchResult 
middleLoop [ ] =
-- no more gc to check, a countermodel has been found
  return CountSat

middleLoop wRecs =
-- wRecs is not empty
-- Select a wRec in wRecs from which a gc will be selected
  do
    pst <- get  -- get prover state
    let mRandomGen = mRandomGenerator pst
        (wRecs_rand,newMRandomGen) = runState  (mShuffleSt wRecs) mRandomGen
    --      if we are in random mode then wRecs_rand is a permutation of wRecs, otherwise wRecs_rand = wRecs
    ( when ( isJust mRandomGen) $ -- update random generator
              modify (\s ->  s{mRandomGenerator =  newMRandomGen} )
       ) -- end when
    -- we select the first wRec in wRecs_rand
    let wRec = head wRecs_rand 
    if  emptyToCheck  wRec then  -- nothing to check in wRec, continue with next wRecs
      middleLoop $ tail wRecs_rand  
    else
      middleLoop_selectedWRec  wRec  (tail wRecs_rand) -- continue middle loop with wRec

middleLoop_selectedWRec :: WorldRec Lit ->   [ WorldRec Lit ]  -> ProverConf SearchResult 


middleLoop_selectedWRec  wRec  wRecs   =
-- wRec is the selected wRec, wRecs the remaining ones
-- wRec contains at least a gc to be selected  
  do
   pst0 <- get  -- get prover state
   let sat = solver pst0
       mRandomGen = mRandomGenerator pst0
       w = worldInRec wRec
       gcs = gcsToCheckRec wRec  -- *not empty*
       (gcs_rand,newMRandomGen) =   runState  (mShuffleSt wRecs) mRandomGen
       -- if we are in random mode then gcs_rand is a permutation of gcs, otherwise gcs_rand=gcs
       -- we select the first gc in gcs_rand   
       gc = head gcs
   ( when ( isJust mRandomGen) $ -- update random generator
              modify (\s ->  s{mRandomGenerator =  newMRandomGen} )
       ) -- end when      
   let notImpls_gc_realAtw_checked  = [ a :-/->: b |  (a :-/->: b)  <- gc `intersect` notImplsCheckedRec wRec ]
       notImpls_gc_realAtw_new =      [ a :-/->: b |  (a :-/->: b)  <- gc \\  notImpls_gc_realAtw_checked ,
                                                                      (model pst0, w) .|>. a :-/->: b  ] 
       notImpls_gc_realAtw = notImpls_gc_realAtw_checked ++  notImpls_gc_realAtw_new
       --  notImpls_gc_realAtw = {  a :-/->: b in gc |   Mod,w |> a -/-> b }
   if  (not . null)  notImpls_gc_realAtw   then
    -- the list   notImpls_gc_realAtw of  a-/-> b is not empty.
   --  Thus Mod,w |> gc and wRec is updated by adding  notImpls_gc_realAtw_new to  notImplsCheckedRec
   --  Continue middle loop
        middleLoop  $  ( updateWRec wRec  gc notImpls_gc_realAtw_new) : wRecs
   else
   -- For every   a -/-> b in gc,  we have  NOT (Mod,w |>  a -/-> b)
   -- Accordingly    NOT( Mod, w |> gc )   
   -- Start inner loop, where gc is the selected general clause
        innerLoop gc  wRec  wRecs   


innerLoop ::  GenClause Lit ->  WorldRec Lit ->  [WorldRec Lit]  -> ProverConf SearchResult 
innerLoop  selectedGc wRec  wRecs   =
-- run inner loop 
--  selectedGg is the selected general clause
--  selectedGc has been selected from wRec,   wRecs are the remaining WorldRecs
  do
    env <- ask  -- get prover environment
    pst <- get  -- get prover state
    let sat = solver pst
        w = worldInRec wRec -- current world
        notImpls = [ a :-/->: b | (a :-/->: b) <- selectedGc ]
        mRandomGen = mRandomGenerator pst
    newWorld_or_newLearnedGc <- evalStateT (innerLoop_callSat  selectedGc notImpls  w)  [] -- outcome of inner loop (world or gc) 
    case newWorld_or_newLearnedGc of  
       NewWorld trueAtms_M ->
      -- found a classical model M such that  w <= M and  M |= a and M |=/= b, with a -/-> b in selectedGc
         do
           let gcsAll =   (intGCs .  initGCSeq) env
               gcsToCheck =  [ gc | gc <- gcsAll ,  trueAtms_M .|=/=. gc ] 
               newWorld = mkWorld 0 trueAtms_M  -- all the world have index 0 
               newModel = addWorld newWorld (model pst)
           modify ( \ s -> s{model = newModel}  )
           -- new iteration of the middle  loop
           middleLoop  ( mkWorldRec newWorld gcsToCheck : updateWRec wRec selectedGc [] :  wRecs)   
       NewLearnedGClause learnedGClause ->
           addLearnedGClause_and_restart learnedGClause  
    


innerLoop_callSat :: GenClause Lit  ->  [GenLit Lit]  -> World Lit  -> StateT [Lit]  ProverConf NewWorld_or_NewLearnedGClause
innerLoop_callSat gc [] w  =
--  notImpls empty, end loop
  do
    collectedAtms <- get
    let notImpls_gc = [ a :-/->: b |  (a :-/->: b) <- gc ]
        gamma =   gc \\  notImpls_gc  -- classical clause 
        learnedGClause =  gamma  `union`  map  Not  collectedAtms
    return $  NewLearnedGClause learnedGClause
  
innerLoop_callSat gc ( (a :-/->: b) : notImpls) w   =
-- iteration of the inner loop processing   a -/-> b
  do
    collectedAtms <- get
    env <- lift $ ask  -- get prover environment
    pst <- lift $ get  -- get prover state
    let sat = solver pst
        wAtms = getWAtms w
    -- @SAT : SAT, w, a |-- b ?  
    isSat <- liftIO $ solve sat ( neg b : a : wAtms ) --  solve :: Solver -> [Lit] -> IO Bool
    if isSat then
      do
        -- found a classical model M such M |= sat U w U {a} and M |=/=  b
        -- trueAtoms_M = atoms in M
        trueAtms_M  <- liftIO $ trueAtmsInSat sat (universe env) 
        return $ NewWorld trueAtms_M
    else
      --  the answer is Yes(assumps)
      do
        -- compute assumps
        xs <- liftIO $ conflict sat   -- conflict :: Solver -> IO [Lit] 
        -- Let xs = x1, ... , xn, then:
        -- SAT |--  x1 v ... v xn and b is one of x1 .. xn 
        let  assumps =  map neg ( xs \\ [b] )
            -- SAT, assumps |--  b
             newCollectedAtms =   collectedAtms `union`  (assumps \\ [a]) -- A*
        put $ newCollectedAtms 
        innerLoop_callSat gc notImpls w   




addLearnedGClause_and_restart :: GenClause Lit -> ProverConf  SearchResult 
addLearnedGClause_and_restart  learnedGClause =
-- main loop from STEP (S9)
-- learnedGClause is the learned clause to be added to the sat solver  
  do
    pst <- get  -- get prover state
    let sat = solver pst
        isClassical_learnedGCClause =  isClassicalGenClause learnedGClause
    lift $ satAddGClause sat  learnedGClause
    proveMainPlain -- ## RESTART 
   



