{-# LANGUAGE TypeOperators, QuasiQuotes #-}
{- quasi quotation
String are enclosed between   [r| and  |]
-}


module Main where

import Data.List
import Text.RawString.QQ
import Data.Maybe
import Data.IORef
import System.IO
import System.Environment -- getArgs
import Control.Monad  
import Text.Printf
import System.CPUTime -- getCPUTime :: IO Integer
import System.Console.GetOpt
import System.Exit
import System.Random
-- import Data.Array.IO




--------
import Language
import ProverTypes
import ParserTPTP
import ParserGC 
import ClausifyGeneralClauses
import Prover
import PlainProver
import Utility
-- import WriteLatex 


-- #######  OPTIONS ######

data Flag
   =  TraceAndLatex                    -- ** NOT USED **
  | MaxTraceLevel                      -- maximum trace level   
  | TraceLevel Int                     -- -tk where k=0 (low),1 (medium), >=2 (high)
  | Clausify                           -- -c
  | ClaessenRosenClausificationFlag    -- -C
  | ProverDebug                        -- -d
  | ClausDebug                         -- -D
  | GeneralClauses                     -- -g
  | Help                               -- -h
  | Seed  Int                          -- -rk  k is the initial seed for the random generator
  | RandomSeed                         -- -r  random initial seed 
  | StrongClausificationFlag             -- -s
  | WeakClausificationFlag             -- -w
  deriving (Eq,Show)

flags =
       [
         Option ['c'] []       (NoArg Clausify)  "Apply the Clausification procedure to the input formula",
         Option ['R'] []       (NoArg ClaessenRosenClausificationFlag)  "Apply the Clausification procedure to the input formula", 
         Option ['d'] []       (NoArg ProverDebug)  "Debug Prover",
         Option ['D'] []       (NoArg ClausDebug)  "Debug Clausifier",
         Option ['g'] []       (NoArg GeneralClauses)  "GeneralClauses",
         Option ['h'] []       (NoArg Help)    "Print this help message",
         Option ['r'] []       (OptArg argRandom "Seed")  "Random",
         Option ['s'] []       (NoArg StrongClausificationFlag)  "Strong clausification",
         Option ['t'] []       (OptArg argTraceLevel "Trace level")  "Trace and Latex",
         Option ['w'] []       (NoArg WeakClausificationFlag)  "Weak clausification"
       ]

argTraceLevel :: Maybe String -> Flag
--  Ex:
--  Just "4"   --->    TraceLevel 4
--  Nothing    ---->   MaxTraceLevel
argTraceLevel (Just k) = TraceLevel $ read  k
argTraceLevel Nothing = MaxTraceLevel

argRandom :: Maybe String -> Flag
-- Ex:
-- Just "123" --->  Seed 123
-- Nothing    --->  RandomSeed
argRandom (Just k) =  Seed $ read k
argRandom Nothing  = RandomSeed


getTraceLevel ::  [Flag] -> Maybe TraceLevel
getTraceLevel args  =
  -- if ( TraceAndLatex `elem` args ) then  Just TraceLevel_high_with_latex
  if ( MaxTraceLevel `elem` args ) then Just TraceLevel_high 
  else
    let mLevel = find isTraceLevel args
    in    
    case mLevel of
     Just (TraceLevel 0) -> Just TraceLevel_low
     Just (TraceLevel 1) -> Just TraceLevel_medium
     Just (TraceLevel k ) -> Just TraceLevel_high  -- k >= 2
     _   -> Nothing

isTraceLevel :: Flag -> Bool
isTraceLevel (TraceLevel _ ) = True
isTraceLevel _               = False

getMRandomSeed ::  [Flag] -> IO (Maybe Int)
getMRandomSeed args  =
  do
    if (RandomSeed `elem` args) then  --  generate a new random seed
        Just <$>  randomIO 
         --randomSeed <- randomIO 
         --return $ Just randomSeed
    else
     do
       let mSeed =   find isSeed args 
       case mSeed of
         Just (Seed k) -> return $ Just k
         _             -> return Nothing  



isSeed :: Flag -> Bool
isSeed (Seed _) = True
isSeed  _       = False    


getClausificationType ::  [Flag] -> ClausificationType

getClausificationType args =
  let claessenR =  ClaessenRosenClausificationFlag  `elem` args
      weak = WeakClausificationFlag `elem` args
      strong =  StrongClausificationFlag `elem` args
  in case (claessenR,weak,strong) of
    (True,_,False)   ->  ClaessenRosenClausification
    (False, True,False) ->  WeakClausification
    (False,False,True)  ->  StrongClausification
    _   ->  ClaessenRosenClausificationStrong  -- default clausification



--------------------------------------------------------------------------------
-- main
-- ###  MAIN ###

main :: IO ()
main =
  do
    (args, files) <- getArgs >>= parseArgs
    let mtraceLev = getTraceLevel args
        inputFile = head files
        clausDebug =  ClausDebug `elem` args
        proverDebug = ProverDebug `elem` args
        noClausification  = GeneralClauses `elem` args 
        clausificationType = getClausificationType args
    mRandomSeed <-    getMRandomSeed args 
    if noClausification then
      withParseFileGC inputFile mtraceLev clausDebug proverDebug mRandomSeed 
    else
      withParseFile  inputFile mtraceLev clausificationType clausDebug proverDebug mRandomSeed


------------------------
-- parse arguments

parseArgs :: [String] -> IO ([Flag], [FilePath])
-- return arguments and input files in the command line 
parseArgs argv = case getOpt Permute flags argv of
        (args,inputFiles,[]) ->
          do
           if Help `elem` args then
              do
                hPutStrLn  stderr  help --   (usageInfo header flags)
                exitWith ExitSuccess
           else if  null inputFiles  then -- no input file
              do
                hPutStrLn stderr $ "No input file" ++ help
                exitWith (ExitFailure 1) 
           else if Clausify `elem` args then  -- only clausify
              do
                let clausificationType = getClausificationType args
                    clausDebug = ClausDebug `elem` args
                onlyClausifyInputFormulas (head inputFiles) clausificationType  clausDebug
                exitWith ExitSuccess 
           else return  (args,inputFiles)  
        (_,_,errs)      ->  -- non-empty list of error messages
          do
            hPutStrLn stderr $ ( concat errs ) ++ help 
            exitWith (ExitFailure 1)
      

help :: String
help = [r|
Usage: intuitRGC [OPTION] FILE

FILE
 text file containing the input formula F (mandatory), see the README file for the syntax

DEFAULT CLAUSIFICATION
Claessen&Rosen clausification with strong clausification (-Rs)

OPTIONS
 -c     only clausify
 -g     the input is a sequent, see the README file for the syntax
 -h     print help
 -r     random execution
 -rN    random execution, with initial generator seed set to N (an integer)
 -t     trace (maximum level) 
 -t0    minimum trace level
 -t1    medium  trace level
 -t2    maximum trace level
 -s     use strong clausification
 -w     use weak clausification
 -R     use original Claessen&Rosen clausification (weak clausification)
|]  -- end string


withParseFile ::  FilePath  ->  Maybe TraceLevel ->  ClausificationType -> Bool -> Bool -> Maybe Int -> IO ()
withParseFile file mtraceLev clausificationType clausDebug proverDebug mRandomSeed  =
  do
    putStrLn $ "+++ intuitRGC"
    putStrLn ("+++ Reading file '" ++ show file ++ "'...")
    mForms <- parseFileTPTP file
    case (mForms,mtraceLev) of
       (Left err,_) -> print err  >> fail "parse error"
       (Right inputForms, Just traceLev )  -> processTrace file clausificationType traceLev clausDebug proverDebug  mRandomSeed inputForms
       (Right inputForms, Nothing) -> processPlain clausificationType  mRandomSeed  inputForms
       


withParseFileGC ::  FilePath  ->  Maybe TraceLevel  -> Bool -> Bool -> Maybe Int -> IO ()
withParseFileGC file mtraceLev  clausDebug proverDebug mRandomSeed  =
 -- parse general clauses, no clausification
  do
    putStrLn $ "+++ intuitRGC"
    putStrLn ("+++ Reading file (general clauses) " ++ show file ++ "'...")
    mGcSeq <- parseFileGcSeq file
    case (mGcSeq,mtraceLev) of
       (Left err,_) -> print err  >> fail "parse error"
       (Right gcSeq, Just traceLev )  -> processTraceGcSeq file  traceLev clausDebug proverDebug  mRandomSeed gcSeq
       (Right gcSeq, Nothing) -> processPlainGcSeq  mRandomSeed  gcSeq
       
-- prover with trace
processTrace :: FilePath -> ClausificationType -> TraceLevel  -> Bool -> Bool -> Maybe Int -> [Input (Form Name)] -> IO ()
processTrace file cType traceLev clausDebug proverDebug mRandomSeed inputForms = 
  do
     putStrLn $ "+++ Clausification ("  ++ show cType ++   ")..."
     startClausify <- getCPUTime
     let (alphas, beta) = parseInputForm inputForms  -- inputForms : (/\alphas) => beta
         (cache,gcSeq) =  clausifyForms  cType clausDebug ( (beta  :=>: Atom mainGoalName)  : alphas )
     putStrLn $ "+++ Created " ++ (show .length . classicalGCs) gcSeq  ++  " classical general clauses, "
                               ++ (show .length . intGCs) gcSeq   ++ " non-classical general clauses, "
                               ++ (show . cacheSize) cache ++ " new atoms"   
     endClausify <- getCPUTime 
     ( when (traceLev >=  TraceLevel_high) $
               do
                   putStrLn $ printfGCSeq id gcSeq
                   putStrLn  $ "=== NEW ATOMS MAP ===\n" ++  printCache cache
                   -- putStrLn  $ "=== SUBSTITUTION ===\n" ++  printCacheSubst cache
            ) -- end when
     putStrLn $ "+++ Proving (intuitRGC)"
     ( when (isJust mRandomSeed)  $
        putStrLn $ "+++ RANDOM (seed = " ++ show (fromJust mRandomSeed) ++ ")"
       )
     hFlush stdout
     startProver <- getCPUTime
     proveProblem  traceLev file clausDebug proverDebug mRandomSeed  gcSeq   emptyCache
     endProver <- getCPUTime
     printTimings  ( Just (startClausify, endClausify) )  (startProver,endProver)
     -- if any nonTrivialIntGC  ( intGCs gcSeq ) then printf "#####  NONTRIVIAL GCSEQ\n"  else  printf "#####  TRIVIAL GCSEQ\n"
     ( when (isJust mRandomSeed) $ 
       putStrLn $ "*** RANDOM SEED ====> " ++ show (fromJust  mRandomSeed)
       )  


processTraceGcSeq :: FilePath -> TraceLevel  -> Bool -> Bool -> Maybe Int -> GenClauseSequent Name -> IO ()
processTraceGcSeq file traceLev clausDebug proverDebug mRandomSeed gcSeq = 
  do
     putStrLn $ printfGCSeq id gcSeq
     putStrLn $ "+++ " ++ (show .length . classicalGCs) gcSeq  ++  " classical clauses, "
                       ++ (show .length . intGCs) gcSeq   ++ " non-classical clauses "
     putStrLn $ "+++ Proving (intuitRGC)"
     ( when (isJust mRandomSeed)  $
        putStrLn $ "+++ RANDOM (seed = " ++ show (fromJust mRandomSeed) ++ ")"
       )
     hFlush stdout
     startProver <- getCPUTime
     proveProblem  traceLev file clausDebug proverDebug mRandomSeed  gcSeq   emptyCache
     endProver <- getCPUTime
     printTimings Nothing (startProver,endProver)
     -- if any nonTrivialIntGC  ( intGCs gcSeq ) then printf "#####  NONTRIVIAL GCSET\n"  else  printf "#####  TRIVIAL GCSET\n"
     ( when (isJust mRandomSeed) $ 
       putStrLn $ "*** RANDOM SEED ====> " ++ show (fromJust  mRandomSeed)
          )  

-- ##  PLAIN PROVER ##

-- prover without trace 
processPlain ::  ClausificationType  -> Maybe Int -> [Input (Form Name)] -> IO ()
processPlain  cType  mRandomSeed inputForms = 
  do
     putStrLn $ "+++ Clausification ("  ++ show cType ++   ")..."
     startClausify <- getCPUTime
     let (alphas, beta) = parseInputForm inputForms  -- inputForms : (/\alphas) => beta
         (cache,gcSeq) =  clausifyForms  cType False ( (beta  :=>: Atom mainGoalName)  : alphas )
     putStrLn $ "+++ Created " ++ (show .length . classicalGCs) gcSeq  ++  " classical general clauses, "
                               ++ (show .length . intGCs) gcSeq   ++ " non-classical general clauses, "
                               ++ (show . cacheSize) cache ++ " new atoms"   
     endClausify <- getCPUTime 
     putStrLn $ "+++ Proving (intuitRGC, no trace)"
     ( when (isJust mRandomSeed)  $
        putStrLn $ "+++ RANDOM (seed = " ++ show (fromJust mRandomSeed) ++ ")"
       )
     hFlush stdout
     startProver <- getCPUTime
     proveProblemPlain   mRandomSeed  gcSeq 
     endProver <- getCPUTime
     printTimings (Just(startClausify, endClausify)) (startProver,endProver)
     ( when (isJust mRandomSeed) $ 
       putStrLn $ "*** RANDOM SEED ====> " ++ show (fromJust  mRandomSeed)       
       )  


processPlainGcSeq ::  Maybe Int -> GenClauseSequent Name -> IO ()
processPlainGcSeq mRandomSeed gcSeq = 
  do
     putStrLn $ "+++ Proving (intuitRGC, no trace)"
     putStrLn $ "+++ " ++ (show .length . classicalGCs) gcSeq  ++  " classical clauses, "
                        ++ (show .length . intGCs) gcSeq   ++ " non-classical clauses "
     ( when (isJust mRandomSeed)  $
        putStrLn $ "+++ RANDOM (seed = " ++ show (fromJust mRandomSeed) ++ ")"
       )
     hFlush stdout
     startProver <- getCPUTime
     proveProblemPlain   mRandomSeed  gcSeq 
     endProver <- getCPUTime
     printTimings Nothing (startProver,endProver)
     ( when (isJust mRandomSeed) $ 
       putStrLn $ "*** RANDOM SEED ====> " ++ show (fromJust  mRandomSeed)
          )  

printTimings ::  Maybe (Integer ,  Integer) ->  (Integer, Integer) -> IO ()
-- print clausification and prover times
-- first arg:   Just(startClausify , endClausify) or Nothing if no clausification has been performed
-- second arg:  (startProver, endProver)
printTimings  mClausifyTimes  (startProver, endProver) =
  do
     let time_clausify = 
           case  mClausifyTimes of
               Just(startClausify,endClausify) ->  (fromIntegral (endClausify - startClausify)) / (10^12)
               Nothing  -> 0
     let  time_prover =  ( fromIntegral (endProver - startProver) ) / (10^12)
     putStrLn   ( concat $ replicate  80 "*" )
     ( when (isJust mClausifyTimes) $
             printf "Clausification time: %0.3f sec\n" (time_clausify :: Double)
      ) --end when
     printf "Prover time:         %0.3f sec\n" (time_prover :: Double)
     ( when (isJust mClausifyTimes) $
            printf "Total time:          %0.3f sec\n" ( (time_clausify + time_prover)  :: Double)
       ) -- end when 



-----------------------

-- ### ONLY CLAUSIFICATION ###

onlyClausifyInputFormulas :: FilePath -> ClausificationType -> Bool -> IO ()
onlyClausifyInputFormulas file  clausificationType  clausDebug  =
  do
    putStrLn ("+++ Reading file '" ++ show file ++ "'...")
    mForms <- parseFileTPTP file
    case mForms of
       Left err -> print err  >> fail "parse error"
       Right inputForms ->
        do
          let form = buildInputForm inputForms    
              (cache,gcSeq) = clausifyForms  clausificationType clausDebug [form] 
          putStrLn $  "=== FORMULA ===\n" ++ printfForm id form    
          putStrLn  $ printfGCSeq id gcSeq    
          putStrLn  $ "=== NEW ATOMS MAPPING ===\n" ++  printCache cache
          -- putStrLn  $ "=== SUBSTITUTION ===\n" ++  printCacheSubst cache

