----------------------------------------------------
--                                                --
-- HyLoRes.FrontEnd.CommandLine:                  --
-- Functions that handle command line processing  --
-- and presentation                               --
--                                                --
----------------------------------------------------

{-
Copyright (C) HyLoRes 2002-2007 - See AUTHORS file

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307,
USA.
-}

module HyLoRes.FrontEnd.CommandLine (
    CmdLineParams, getCmdLineParams, defaultParams,

    usage,

    showHelp,
    quietMode,
    filename,
    mustLogState, mustLogRules, mustLogComm, genModel, useBWSubs,
    complexityStr, selFuncStr,
    maxtimeout, configureStats, workerCount,dispatchAlg
)

where

import System.Environment    ( getArgs )
import System.Console.GetOpt ( OptDescr(..), ArgDescr(..), ArgOrder(..),
                               getOpt, usageInfo )
import System.Directory      ( getHomeDirectory, doesFileExist )
import System.FilePath       ( (</>) )

import Control.Monad       ( liftM )
import Control.Monad.Error ( MonadError(..) )
import Control.Applicative ( (<$>) )

import Data.Char  ( isDigit )
import Data.Maybe ( isJust )

import HyLoRes.ClauseSet.Clauses  ( ComplexityParamStr )
import HyLoRes.Clause.SelFunction ( SelFuncString )
import HyLoRes.Statistics ( StatsValues, mkStatsValues,
                            UniqueMetric,
                            rawClausesGenerated,
                            nonFwSubsumedClausesGenerated,
                            premisesSubsumedByConsequents,
                            ruleApplicationCount,
                            averageGivenClauseSize,
                            lateSubsumedClauses )

data CmdLineParams = CLP {
           showHelp      :: Bool,
           filename      :: Maybe FilePath,
           mustLogState  :: Bool,
           mustLogRules  :: Bool,
           mustLogComm   :: Bool,
           genModel      :: Maybe FilePath,
           quietMode     :: Bool,
           complexityStr :: ComplexityParamStr,
           selFuncStr    :: SelFuncString,
           useBWSubs     :: Bool,
           maxtimeout    :: Int,
           workerCount   :: Maybe Int,
           dispatchAlg   :: String,
           statsStr      :: String
         } deriving (Show)

type CLPModifier   = CmdLineParams -> Either ParsingErrMsg CmdLineParams
type ParsingErrMsg = String

parseCmds :: [String] -> CmdLineParams -> Either ParsingErrMsg CmdLineParams
parseCmds argv clp = case getOpt RequireOrder options argv of
                       (clpMods, [],  []) -> thread clpMods clp
                       (      _,unk,  []) -> fail $ "Unknown option: " ++
                                                   unwords unk
                       (     _,   _,errs) -> fail $ unlines errs


thread :: Monad m => [a -> m a] -> a -> m a
thread = foldr (\f g -> \a -> f a >>= g) return

options :: [OptDescr CLPModifier]
options =
  [Option ['h','?']
          ["help"]
          (NoArg $ \c -> return c{showHelp = True})
          "display this help and exit",
   Option ['f']
          ["input-file"]
          (ReqArg ((not . null) ?-> \s c -> return c{filename = Just s}) "FILE")
          "obtain input formulas from FILE instead of STDIN",
   Option ['q']
          ["quiet", "silent"]
          (NoArg $ \c -> return c{quietMode = True})
          "suppress all normal output",
   Option ['t']
          ["timeout"]
          (ReqArg setTimeout "T")
          "run for at most T seconds",
   Option ['n']
          ["worker-count"]
          (ReqArg setWorkerCount "N")
          (unlines["set SMP mode to on, running N workers (experimental)",
                   "default is " ++
                    maybe "off" show (workerCount defaultParams)]),
   Option ['m']
          ["save-model"]
          (ReqArg ((not . null) ?-> \s c -> return c{genModel = Just s}) "FILE")
          (unlines [
          "if the formulas are satisfiable, output a model",
          "to FILE"]),
   Option ['s']
          ["log-state"]
          (NoArg $ \c -> return c{mustLogState = True})
          "log the internal state (clauses, inUse and new)",
   Option ['r']
          ["log-rules"]
          (NoArg $ \c -> return c{mustLogRules = True})
          "log rule applications",
   Option []
          ["log-comm"]
          (NoArg $ \c -> return c{mustLogComm = True})
          "log communication between execution units",
   Option ['S']
          ["statistics"]
          (ReqArg setStats "PAT")
          (unlines [
           "PAT configures the collecting of statistics.",
           "A valid PAT is of the form:",
           "",
           "   METRICS:INTERVAL:METRICS",
           "",
           "The `:INTERVAL:METRICS` argument is optional",
           "and declares metrics that will be printed at",
           "regular intervals (e.g. `:100:r' shows the",
           "number of rules applied so far, every 100",
           "iterations of the given clause algorithm).",
           "",
           "METRICS is made of one or more of the following",
           "values:",
           "  g = raw number of clauses generated",
           "  G = number of clauses that made it to the",
           "      Clauses queue (ie, not forward subsumed)",
           "  c = number of premises subsumed by their",
           "      consequents",
           "  r = number of rules applied",
           "  a = average number of formulas in the given",
           "      clause",
           "  l = late subsumed clauses",
           "",
           "The default is `" ++ statsStr defaultParams ++ "'",
           ""]),
   Option ['o']
          ["select-given"]
          (ReqArg setSelectGiven "PAT")
          (unlines [
          "PAT configures the criteria for the given clause",
          "selection. A valid PAT is a combination of any",
          "of the following values (priority in PAT goes",
          "from left to right):",
          "  s = size of the clause",
          "  v = number of literals occurring",
          "      in the clause",
          "  V = number of literals in",
          "      the distinguished formula",
          "  d = maximum modal depth of",
          "      formulas in the clause",
          "  D = maximum modal depht of the",
          "      distinguished formula",
          "  l = minimum prefix level of",
          "      formulas in the clause ",
          "  L = minimum prefix level of",
          "      the distinguished formula",
          "  M = 1 if the distinguished formula",
          "      is an @diamond, and 0 otherwise",
          "  B = 1 if the distinguished formula",
          "      is an @-box, and 0 otherwise",
          "",
          "The default is `" ++ complexityStr defaultParams ++ "'",
          ""]),
   Option []
          ["no-backwards-subsumption"]
          (NoArg $ \c -> return c{useBWSubs = False})
          "turn off backwards subsumption check",
   Option ['D']
          ["dispatch-alg"]
          (ReqArg setDispatchAlg "ALG")
          (unlines [
          "ALG configures the dispatch algorithm used to distribute nominals to workers.",
          "The valid ALG are:",
          "  HASH = uses a simple hash function",
          "  RROBIN = uses a round-robin assigment",
          "  LOAD  = assigns to the loader with less clauses processed",
          ""]),
   Option ['F']
          ["select-func"]
          (ReqArg setSelFunc "PAT")
          (unlines [
          "PAT configures the selection function to use.",
          "A valid PAT is a combination of any of the",
          "following values:",
          "  n = pick a negative literal",
          "  a = pick a conjunction",
          "  o = pick a disjunction",
          "  d = pick a diamond (but not a relation)",
          "  b = pick a box",
          "",
          "The selection function will pick a formula that",
          "matches any of the above criterias, but in the",
          "order they occur in PAT; the leftmost is the",
          "one preferred. If there were more than one",
          "candidates in the clause, the minimum candidate",
          "will be preferred. If PAT starts with an `L',",
          "then among all the candidates, the selection",
          "function will prefer the minimum among those",
          "whose prefix' level is minimum",
          "",
          "The default is `" ++ selFuncStr defaultParams ++ "'"])]

(?->) :: (String -> Bool) -> (String -> CLPModifier) -> String -> CLPModifier
p ?-> m = \s -> if (not $ null s) && p s
                  then m s
                  else \_ -> throwError ("Invalid argument: '" ++ s ++ "'")


setTimeout :: String -> CLPModifier
setTimeout = (all isDigit) ?-> \s c -> return c{maxtimeout = read s}

setWorkerCount :: String -> CLPModifier
setWorkerCount = (all isDigit) ?-> \s c -> return c{workerCount = Just $ read s}

setDispatchAlg :: String -> CLPModifier
setDispatchAlg = isValid ?-> \s c -> return c{dispatchAlg = s}
   where isValid "HASH" = True
         isValid "RROBIN" = True
         isValid "LOAD" = True
         isValid _ = False

setSelectGiven :: String -> CLPModifier
setSelectGiven = all (`elem` complexityStrVal) ?->
                   \s c -> return c{complexityStr = s}

complexityStrVal :: String
complexityStrVal = "svVdDlLMB"


setSelFunc :: String -> CLPModifier
setSelFunc = isValid ?-> \s c -> return c{selFuncStr = s}
    where isValid ('L':xs) = all (`elem` selFuncVal) xs
          isValid  xs      = all (`elem` selFuncVal) xs

selFuncVal :: String
selFuncVal = "naodb"


setStats :: String -> CLPModifier
setStats = (isJust . parseStats) ?->
             \s c -> return c{statsStr = s}

defaultParams :: CmdLineParams
defaultParams = CLP {showHelp      = False,
                     filename      = Nothing,
                     mustLogState  = False,
                     mustLogRules  = False,
                     mustLogComm   = False,
                     genModel      = Nothing,
                     quietMode     = False,
                     complexityStr = "sDMBLV",
                     selFuncStr    = "dboan",
                     useBWSubs     = True,
                     maxtimeout    = 0,
                     workerCount   = Nothing,
                     dispatchAlg   = "RROBIN",
                     statsStr      = "rgGl:0:ac"}


getCmdLineParams :: IO (Either ParsingErrMsg CmdLineParams)
getCmdLineParams =
    do let clp_0 = defaultParams
       m_hyloresrc <- findHyLoResRc
       parse_clp_1 <- case m_hyloresrc of
                        Nothing -> return $ return clp_0
                        Just f  -> do rc_args <- words <$> readFile f
                                      return $  parseCmds rc_args clp_0
                                              `catchError`
                                                (\e -> fail $ f ++ ":\n" ++ e)
       --
       cmdline_args   <- getArgs
       --
       return $ do clp_1 <- parse_clp_1
                   parseCmds cmdline_args clp_1

hyloresrc :: FilePath
hyloresrc = ".hyloresrc"

findHyLoResRc :: IO (Maybe FilePath)
findHyLoResRc =
    do existsInCurrent <- doesFileExist hyloresrc
       if existsInCurrent
         then return (Just hyloresrc)
         else do
             home <- getHomeDirectory
             let inHome = home </> hyloresrc
             --
             existsInHome <- doesFileExist inHome
             if existsInHome then return (Just inHome) else return Nothing


usage :: String -> String
usage header = unlines [
    usageInfo header options,
    "",
    "If a file called `" ++  "." </> hyloresrc ++ "' or `" ++ "~" </> hyloresrc
    ++ "' exists, it will be scanned for arguments first"
    ]


metrics :: [(Char, IO UniqueMetric)]
metrics = [('g', rawClausesGenerated),
           ('G', nonFwSubsumedClausesGenerated),
           ('c', premisesSubsumedByConsequents),
           ('r', ruleApplicationCount),
           ('a', averageGivenClauseSize),
           ('l', lateSubsumedClauses)]

parseStats :: String -> Maybe (String, Maybe (Int, String))
parseStats s
    | allMetricsExist fmIds &&
      (null opIms ||
       if (null inter)
           then (null imIds)
           else (all isDigit inter &&
                 allMetricsExist imIds')) = Just (fmIds,inspectionStats)
    | otherwise                           = Nothing
    where (fmIds,opIms)   = break (== ':') s
          (inter,imIds)   = break (== ':') (tail opIms)
          imIds'          = tail imIds
          allMetricsExist = all (`elem` validMetrics)
          validMetrics    = (fst . unzip) metrics
          inspectionStats = if ( null inter )
                                then Nothing
                                else Just (read inter, imIds)



{- statistics: Given
    - a CmdLineParams clp with a valid statistics string,
      builds a proper Statistics instance

   A valid string is a sequence of chars that represent metrics, optionally
   followed by a colon, a number, another colon, and the sequence of
   inspection metrics
-}
configureStats :: CmdLineParams -> IO StatsValues
configureStats clp =
    do
      let Just (fmIds,ims) = parseStats (statsStr clp)
      --
      fms   <- filterMetrics fmIds
      iifms <- maybe (return Nothing) (liftM Just) $ fmap (\(a,b) -> return . (,) a =<< filterMetrics b) ims
      --
      mkStatsValues fms iifms

filterMetrics :: String -> IO [UniqueMetric]
filterMetrics s = mapM snd (filter (\(c,_) -> c `elem` s) metrics)
