{-# LANGUAGE TypeOperators #-}
module Prover (
    proveProblem  -- TraceLevel -> FilePath  -> Bool -> Bool -> Maybe Int -> GenClauseSequent Name  -> Cache -> IO ()
                  -- prover with trace and derivations/countermodels
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
-- import WriteLatex
-- import WriteModelGraphviz
-- import WriteMakeFile


{-
NOTE:

GenLit: literal in the objecyt language
   Lit: literals of the SAT-solver language
-}



-- ########################################################
-- #######        PROVER  WITH  TRACE              ########
-- ########################################################

proveProblem :: TraceLevel -> FilePath  -> Bool -> Bool -> Maybe Int -> GenClauseSequent Name  -> Cache -> IO ()
-- tracelLevel:  trace level
-- file: name of the input file
-- debug:  true to debug the prover
-- mRandomSeed: 'Just k' for  random computation with initial seed k, Nothing for non-random computation  
-- gcSeq:  problem to solve
-- cache: map name |--> simpleForm
proveProblem traceLev file  calsuDebug proverDebug mRandomSeed gcSeq  cache = 
 do
  let baseName = takeBaseName file
  let msgSizeW = "Size of the set W (= number of worlds in W) at the end of every iteration of the main loop : "
  (proverEnv,initialProverState)  <- initProblem traceLev baseName proverDebug mRandomSeed gcSeq cache
  ( res,finalProverState, _ ) <-  runRWST  proveMain  proverEnv  initialProverState  
  let  learnedGClauses = learnedGCs finalProverState
       -- traceName =  "trace_"  ++ baseName
       -- derName= "derivation_"  ++ baseName
       -- modelName= "model_"  ++ baseName
       -- dirName = "out-" ++ baseName
       -- texTraceFile = combine dirName (addExtension traceName ".tex")
       -- texDerFile = combine dirName (addExtension derName ".tex")
       -- gvFile =  combine dirName (addExtension modelName ".gv")
       -- makeFile = combine dirName  "Makefile"
       -- msgMake = (concat $ replicate  80 "*") ++
       --          "\n---> Output files are in the directory '" ++    dirName  ++ "'" ++
       --          "\n---> Move into directory '" ++ dirName ++ "' and run command 'make' to compile them" 
  case res of
       Valid  ->  -- valid
         do
           putStrLn "+++ RESULT: Valid (in IPL)"
           putStrLn ( writeStatistics  proverEnv finalProverState )
           ( when (countRest finalProverState > 0 &&  traceLev >= TraceLevel_medium ) $
             putStrLn $ msgSizeW
                 ++ show (reverse (modelsSize finalProverState)) 
            ) -- end when 
           ( when(traceLev >= TraceLevel_high_with_latex) $
             do
                putStrLn ".... NOT IMPLEMENTED YET ...."
               -- createDirectoryIfMissing True dirName  
               -- writeFile texTraceFile (writeLatexTrace  proverEnv finalProverState)
               -- writeFile texDerFile (writeLatexDerivation proverEnv finalProverState)  
               -- writeFile makeFile (writeMakeFile_valid traceName derName)
               -- putStrLn msgMake
            ) -- end when
       CountSat ->
         do
           putStrLn "+++ RESULT: CounterSatisfiable (in IPL)"
           putStrLn ( writeStatistics  proverEnv finalProverState )
           ( when ( traceLev >= TraceLevel_medium ) $
             putStrLn $ msgSizeW
                 ++ show (reverse (modelsSize finalProverState)) 
            ) -- end when
           ( when (traceLev >= TraceLevel_high_with_latex) $
             do
                putStrLn ".... NOT IMPLEMENTED YET ...." 
                -- createDirectoryIfMissing True dirName             
                -- writeFile texTraceFile (writeLatexTrace proverEnv finalProverState)
                -- writeFile gvFile (writeModelGraphviz proverEnv finalProverState )
                -- writeFile makeFile (writeMakeFile_countsat traceName modelName)
                -- putStrLn msgMake
            ) -- end when


-- initial setup
initProblem :: TraceLevel -> FilePath  ->  Bool -> Maybe Int ->  GenClauseSequent Name  -> Cache ->  IO (ProverEnv,ProverState)
-- tracelLevel:  trace level
-- file: name of the input file
-- proverDebug:  true to debug the prover
-- mRandomSeed: 'Just k' for  random computation with initial seed k, Nothing for non-random computation  
-- gcSeq:  sequent to prove
-- cache: map name |--> simpleForm
initProblem traceLev file proverDebug mRandomSeed gcSeq  cache =
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
  let  proverEnv = mkProverEnv file  univ  gcSeq_satLit_rand   ltToNm_map  traceLev proverDebug cache
       initialProverState =  mkProverState sat mRandomGen2
  return  (proverEnv,initialProverState )



proveMain :: ProverConf SearchResult 
proveMain  =
-- main loop 
  do
    env <- ask  -- get prover environment
    pst <- get  -- get prover state
    let sat = solver pst
        gcSeq = initGCSeq env
        rightL = rightAtm gcSeq  
        ltToNm = litToName env
        cntSat = countSat pst
        cntRest =  countRest pst
        traceLev = traceLevel env
        proverDebug = runDebugger env
        mRandomGen = mRandomGenerator pst
        -- step_askSatR = AskSatR(cntSat,cntRest, rightL)
    ( when( traceLev >= TraceLevel_high ) $
         liftIO $ putStrLn $ printStep (cntSat + 1) ++ printfAsk ltToNm  Nothing cntRest  rightL
       ) -- end when
    -- @SAT:  SAT |-- rightL ?
    isSat <- lift $ solve sat [  neg rightL ]  --  solve :: Solver -> [Lit] -> IO Bool
    -- update prover state
    modify ( \ s -> s{countSat = countSat s + 1 }  )
    -- when( traceLev >= TraceLevel_high )(
    --    modify ( \ s -> s{trace = addStep step_askSatR  (trace s) } )
    --   )
    if isSat then
     -- found a classical model M such M |= sat and M |=/=  rightL
     -- trueAtoms_M = atoms in M
     do
        -- ### STEP (S2) ##
         trueAtms_M <- lift $ trueAtmsInSat sat (universe env) 
         let wIndex = nextWorldIndex pst -- index of the new world
             newWorld = mkWorld wIndex trueAtms_M  
             newModel = addWorld newWorld emptyModel
             gcsToCheck =  [ gc | gc <- intGCs gcSeq , trueAtms_M .|=/=.  gc  ] 
             (gcsToCheck_rand,newMRandomGen) =    runState  (mShuffleSt  gcsToCheck) mRandomGen
             -- if we are in random mode then gcsToCheck_rand is a permutation of gcsToCheck, otherwise gcsToCheck_rand=gcsToCheck
             newWorldRec = mkWorldRec newWorld gcsToCheck_rand
         ( when ( isJust mRandomGen) $  -- update random generator
               modify (\s ->  s{mRandomGenerator =  newMRandomGen} )
           ) -- end when
         modify ( \ s -> s{nextWorldIndex = wIndex + 1 , model = newModel} )
         ( when (traceLev >= TraceLevel_high ) $
           do
             -- modify ( \s -> s{trace = addStep step_foundW (trace s) } )
             let iGCs = (intGCs . initGCSeq) env
             liftIO $ putStrLn  $ ">>> NO( " ++ printfAtmsSortedBrace ltToNm trueAtms_M ++ " )"
             liftIO $ putStrLn $ printfAddedWorld ltToNm (cntSat + 1) newWorld  newModel  iGCs
            ) -- end when
         ( when proverDebug $ 
                 liftIO $ putStrLn $ "TO CHECK IN " ++  printW wIndex ++  "\n" ++ printfGClauses ltToNm gcsToCheck
             )  
         middleLoop [ newWorldRec ] -- start middle loop 
       else
      --  the answer is Yes({}), thus   sat |-- rightL
      --  Hence gcSeq is proved
        do 
          -- update prover state
          modify ( \ s -> s{isValidForm = True  }  )
          -- let  step_valid =  ProvedSat(cntRest,[], rightL )
          ( when (traceLev >= TraceLevel_medium ) $
              modify( \ s -> s{modelsSize =  sizeModel (model s) : (modelsSize s)} )
             ) -- end when
          ( when( traceLev >= TraceLevel_high ) $
            do
               liftIO $ putStrLn $ ">>> YES( {} )"   
               -- modify ( \ s -> s{trace = addStep step_valid (trace s)} )
            ) -- end when
          return  Valid    


middleLoop :: [ WorldRec Lit ]  -> ProverConf SearchResult 

{-

Let gc = [d1 ... dl ,  ~c1 ... ~cm,  a1 -/-> b1  ... an -/-> bn ] (general clause)
Let Mod be the current model (set of worlds)  and w a world in Mod

(1)  w |== gc (classical validity) IFF

     - for every  d in gc,  w |==  d  (namely, d \in w)
     - for every ~c in gc,  w |=/= c  (namely, c \not\in w)

(2)    Mod, w |>  a -/-> b IFF
       there is w' in Mod s.t. w <= w' and w' |== a and w' |=/= b 
 

(3)  Mod, w |>  gc IFF either (A) or (B) holds:

    (A)  w |== gc   *OR*
    (B)  there is  a -/-> b in gc  such that Mod, w |> a -/-> b

----------------

The argument is a list of wRecs = [ wRec1,  wRec2,  .... ]   

For every element

  wRec = {   worldInRec = w , gcsToCheckRec = gcs ,   notImplsCheckedRec = notImpls }

in the list we assume that (Mod is the current model):

*  For every gc in gcs,    w  |==  gc

*  For every   a-/-> b in notImpls,  Mod, w |>  a-/->b

 gcsToCheck collects the gc to check

-}

middleLoop [ ] =
-- no more gc to check, a countermodel has been found 
 do 
  env <- ask  -- get prover environment
  let traceLev = traceLevel env
  ( when( traceLev >= TraceLevel_medium ) $
     modify( \ s -> s{modelsSize =  sizeModel (model s) : (modelsSize s)} )
   ) -- end when
  return CountSat

middleLoop wRecs =
-- wRecs is not empty
-- Select a wRec in wRecs from which a gc will be selected
  do
    env <- ask  -- get prover environment
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
   env <- ask   -- get prover environment 
   pst0 <- get  -- get prover state
   let sat = solver pst0
       cntSat =  countSat pst0
       cntRest = countRest pst0
       ltToNm = litToName env
       traceLev = traceLevel env
       proverDebug = runDebugger env
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
   ( when proverDebug $
         do
           liftIO $ putStrLn $ printfWorldRecs  ltToNm  ( wRec  : wRecs )    
           liftIO $ putStrLn $ "-- notImpls_gc_realAtw_checked: " ++ printfGClause  ltToNm notImpls_gc_realAtw_checked    
           liftIO $ putStrLn $ "-- notImpls_gc_realATw_new: " ++ printfGClause  ltToNm notImpls_gc_realAtw_new
           liftIO $ putStrLn $ "-- notImpls_gc_realAtw: " ++ printfGClause  ltToNm notImpls_gc_realAtw
     ) -- end when
   if  (not . null)  notImpls_gc_realAtw   then
    -- the list   notImpls_gc_realAtw of  a-/-> b is not empty.
   --  Thus Mod,w |> gc and wRec is updated by adding  notImpls_gc_realAtw_new to  notImplsCheckedRec
   --  Continue middle loop
        middleLoop  $  ( updateWRec wRec  gc notImpls_gc_realAtw_new) : wRecs
   else
   -- For every   a -/-> b in gc,  we have  NOT (Mod,w |>  a -/-> b)
   -- Accordingly    NOT( Mod, w |> gc )   
   -- Start inner loop, where gc is the selected general clause
     do
      -- let  step_selected = Check(getWIndex w,  ((a:->b):->c) )
      ( when ( traceLev >= TraceLevel_high ) $
        do
          -- modify  ( \ s ->s{ trace = addStep  step_selected  (trace s) } )
          liftIO $ putStrLn $   "MIDDLE LOOP: selected " ++ printfPairWorldGC ltToNm (w,gc)
       ) -- end when
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
        ltToNm = litToName env
        cntSat = countSat pst
        cntRest =  countRest pst
        w = worldInRec wRec -- current world
        notImpls = [ a :-/->: b | (a :-/->: b) <- selectedGc ]
        traceLev = traceLevel env
        proverDebug = runDebugger env
        mRandomGen = mRandomGenerator pst
        -- step_askRW =  AskSatRW(cntSat,cntRest,  getWIndex w, a, b)
    newWorld_or_newLearnedGc <- evalStateT (innerLoop_callSat  selectedGc notImpls  w)  [] -- outcome of inner loop (world or gc) 
     -- ( when( traceLev >= TraceLevel_high ) $
    --   modify (  \ s -> s {trace = addStep step_askRW (trace s) } )
    --   ) -- end when 
    case newWorld_or_newLearnedGc of  
       NewWorld trueAtms_M ->
      -- found a classical model M such that  w <= M and  M |= a and M |=/= b, with a -/-> b in selectedGc
         do
           let gcsAll =  (intGCs .  initGCSeq) env
               gcsToCheck =  [ gc | gc <- gcsAll ,  trueAtms_M .|=/=. gc ] 
               wIndex = nextWorldIndex pst -- index of the new world
               newWorld = mkWorld wIndex trueAtms_M  
               newModel = addWorld newWorld (model pst)
               -- step_foundW = NewWorld(wk,trueAtms)
           modify ( \ s -> s{nextWorldIndex = wIndex + 1 , model = newModel}  )
           ( when( traceLev >= TraceLevel_high ) $
             do
               -- update prover state
               -- modify ( \ s -> s{trace = addStep step_foundW (trace s) } )
               let iGCs = (intGCs . initGCSeq) env
               liftIO $ putStrLn $ ">>> NO( " ++ printfAtmsSortedBrace ltToNm trueAtms_M ++ " )" 
               liftIO $ putStrLn $ printfAddedWorld ltToNm cntSat newWorld  newModel iGCs
              ) -- end when
           ( when proverDebug $ 
                 liftIO $ putStrLn $ "TO CHECK IN " ++  printW wIndex ++  "\n" ++ printfGClauses ltToNm gcsToCheck
             )  
           -- new iteration of the middle  loop
           middleLoop  ( mkWorldRec newWorld gcsToCheck : updateWRec wRec selectedGc [] :  wRecs)
       NewLearnedGClause learnedGClause ->
        do
          ( when( traceLev >= TraceLevel_high ) $
               do
            -- update prover state  
            -- modify ( \ s -> s{trace = addStep step_proved (trace s)  })
               liftIO $ putStrLn $ "last selected clause:   "   ++  printfGClause ltToNm selectedGc
           ) -- end when  
          addLearnedGClause_and_restart learnedGClause  
    


innerLoop_callSat :: GenClause Lit  ->  [GenLit Lit]  -> World Lit  -> StateT [Lit]  ProverConf NewWorld_or_NewLearnedGClause
{-

innerLoop_callSat gc  notImpls w

Run the inner loop
- gc is the  selected general clause
- notImpls is the list of formulas a -/-> b  to be  processed 
- w is the current world

In StateT, [Lit] are the atoms (assumptions) collected in the inner loop


Return:

* NewWorld trueAtms_M
  
   trueAtms_M are the atoms in the new world

* NewLearnedGClause learnedGc   

  learnedGc is the learned gc


-}
innerLoop_callSat gc [] w  =
--  notImpls empty, end loop
{-
Let

-  gc =  gamma v  (a1 :-/->: b1) v ...  v (an :-/->: bn)

   with gamma a classical clasues

-  collectedAtms = set of the atoms collected in the inner loop

Then:

 learnedGClause = gamma v (  \/ ~a : a \in assumps ) 


-}
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
        ltToNm = litToName env
        cntSat = countSat pst
        cntRest =  countRest pst
        traceLev = traceLevel env
        wAtms = getWAtms w
        wIndex = getWIndex w
    -- @SAT : SAT, w, a |-- b ?  
    isSat <- liftIO $ solve sat ( neg b : a : wAtms ) --  solve :: Solver -> [Lit] -> IO Bool
    ( when( traceLev >= TraceLevel_high ) $
      do
        liftIO $ putStrLn ( "INNER LOOP: selected "  ++ printfGLit ltToNm  (a :-/->: b) ) 
        liftIO $ putStrLn (printStep (cntSat + 1) ++ 
            printfAsk  ltToNm  (Just(a:-/->:b  , wIndex))  cntRest b  )
      ) -- end when  
    lift $ modify ( \ s -> s{countSat = countSat s + 1 })
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
        ( when( traceLev >= TraceLevel_high ) $
            do
               liftIO $ putStrLn $ "YES( " ++  printfAtmsSortedBrace ltToNm assumps   ++    " )"
               liftIO $ putStrLn $ "A* = " ++  printfAtmsSortedBrace ltToNm newCollectedAtms
         ) -- end when
        put $ newCollectedAtms 
        innerLoop_callSat gc notImpls w   




addLearnedGClause_and_restart :: GenClause Lit -> ProverConf  SearchResult 
addLearnedGClause_and_restart  learnedGClause =
-- main loop from STEP (S9)
-- learnedGClause is the learned clause to be added to the sat solver  
  do
    env <- ask  -- get prover environment
    pst <- get  -- get prover state
    let sat = solver pst
        cntSat =  countSat pst
        cntRest = countRest pst
        ltToNm = litToName env
        traceLev = traceLevel env
    lift $ satAddGClause sat  learnedGClause
    modify( \s -> s{
              learnedGCs =  learnedGClause :  (learnedGCs s),
              countRest = countRest pst + 1,
              modelsSize =  sizeModel (model s) : (modelsSize s)
          } ) 
    ( when( traceLev >= TraceLevel_high ) $
      do
         -- update prover state
        -- modify  ( \ s -> s{trace = addStep step_newc (trace s) } )
        let  step = cntSat + 1
        liftIO $ putStrLn  $  "learned classical clause:   " ++  printfGClause ltToNm learnedGClause
        liftIO $ putStrLn (  printGamma   (cntRest + 1) ++ " = " ++ printGamma cntRest ++ " + learned clause " ) 
        liftIO $ putStrLn ( "###########  RESTART " ++ show (cntRest + 1)  ++
                          "  ###########" )
       )-- end when
    proveMain -- ## RESTART 
   
-- #############################################################à


writeStatistics :: ProverEnv -> ProverState -> String
writeStatistics env pst =
  let mod =
        if (isValidForm pst) then "" else
          "\nWorlds in the countermodel: " ++ (show . sizeModel . model) pst
      initGcSet = initGCSeq env
      cAtms = (length . universe) env   
      cNewAtms = (cacheSize . cacheEnv) env 
  in 
  "Classical general clauses: " ++   (show . length . classicalGCs) initGcSet  
  ++ "\nNon-classical general clauses: " ++ (show . length . intGCs) initGcSet  
  ++ "\nAtoms: " ++ show cAtms ++ " (" ++ show cNewAtms ++ " new)" 
  ++ "\nCalls to the SAT-solver: " ++ ( show .countSat) pst  
  ++ "\nRestarts: " ++  ( show . countRest ) pst
  ++ mod




printfAsk :: (Lit -> Name) -> Maybe(GenLit Lit,Int) -> Int -> Lit -> String
printfAsk   ltToNm appliedRule cntRest right  =
  let left = case appliedRule of
        Nothing -> ""
        Just(a :-/->: b ,k ) -> ", " ++ printW k ++ ", " ++ ltToNm a
  in
  "@SAT: " ++ printGamma  cntRest  ++  left ++ " |-- " ++ ltToNm right ++ " ?" 


printW :: Int -> String
printW k = "W" ++ show k

printGamma :: Int -> String
printGamma k = "Gamma" ++ show k



printStep :: Int -> String
printStep k = "[" ++ show k ++ "] "

printfAddedWorld :: Ord a => (a -> Name) ->  Int -> World a -> Model a -> [GenClause a] -> String
printfAddedWorld ltToNm cntSat newW newM iGCs  =
          "NEW WORLD: " ++ printW (getWIndex newW) ++
           -- printfWorld ltToNm newW ++ "\n" ++
           "\nCURRENT MODEL:\n" ++ printfModel ltToNm newM ++
           "\nSELECTABLE PAIRS:\n"  ++  printfSelectablePairs ltToNm newM iGCs

-----------------
-- debug
printfWorldRec  ::   (Lit -> Name)  -> WorldRec Lit -> String
printfWorldRec ltToNm wRec =
  let toCheck = gcsToCheckRec wRec
      checked_notImpls = notImplsCheckedRec wRec
  in    
  "\n<<-- BEGIN RECORD--\n" 
  ++ "World: " ++ printfWorld ltToNm (worldInRec wRec) 
  ++ "\n--To Check: " ++   prettyPrint  toCheck   (printfGClauses ltToNm toCheck)
  ++ "\n--Checked (notImpls): " ++ prettyPrint checked_notImpls  (printfGClause ltToNm checked_notImpls )        
  ++"-- END RECORD -->>"
  where prettyPrint xs ys =   -- to avoid empty lines
          if null xs then "\n" else "\n" ++ ys

printfWorldRecs  ::   (Lit -> Name)  -> [WorldRec Lit] -> String
printfWorldRecs ltToNm wRecs =
  "####################   WORLD RECS ###################"
   ++ concatMap   (printfWorldRec ltToNm)  wRecs ++
   "\n####################################################"
 

printfSelectablePairs :: Ord a => (a -> Name)  -> Model a ->  [GenClause a] -> String
printfSelectablePairs ltToNm mod iGCs =
  let selectablePairs = [ (w,gc) | w <- getWorlds mod , gc <- iGCs  , not ( (mod,w)  .|>>. gc ) ]
      selectablePairs_str = map (printfPairWorldGC ltToNm) selectablePairs 
  in
    printfListNl id  selectablePairs_str


printfPairWorldGC :: (a -> Name)  -> (World a,  GenClause a ) -> String
printfPairWorldGC ltToNm (w, gc) =
   "< " ++ printW  (getWIndex w)  ++ " , " ++ printfGClause ltToNm gc  ++ " >" 









