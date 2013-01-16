module Main ( main ) where

import Data.List ( tails )
import qualified Data.Set as Set

import Control.Applicative ( (<$>) )
import HyLo.Util           ( sequenceUntil )

import System.Exit        ( exitFailure          )
import System.FilePath    ( (</>)                )
import System.Directory   ( getDirectoryContents )
import System.Environment ( getArgs              )

import HyLo.Model
import HyLo.Model.Herbrand
import HyLo.InputFile

import HyLoRes.Core.Worker.Base ( Result(..) )

import HyLoRes.FrontEnd.CommandLine
import qualified HyLoRes.Main as HyLoRes

type NumWorkers = Int

main :: IO ()
main =
  do (sat_dir, unsat_dir) <- parseArgs
     --
     sat_files   <- frmFiles sat_dir
     unsat_files <- frmFiles unsat_dir
     --
     let (serial,n2) = (Nothing, Just 2)
     let all_tests   = concat [map (runExpecting Sat   serial) sat_files,
                               map (runExpecting Sat   n2)     sat_files,
                               map (runExpecting Unsat serial) unsat_files,
                               map (runExpecting Unsat n2)     unsat_files]
     --
     success <- and <$> sequenceUntil not all_tests
     if success
       then putStrLn "SUCCESS"
       else putStrLn "FAILURE" >> exitFailure

data Expected = Sat | Unsat deriving (Eq, Show)

parseArgs :: IO (FilePath, FilePath)
parseArgs = go =<< getArgs
    where go [sd, ud] = return (sd, ud)
          go _        = fail "Required args: <sat dir> <unsat dir>"

frmFiles :: FilePath -> IO [FilePath]
frmFiles dir = map (dir </>) . filter (endsWith ".frm") <$>
                   getDirectoryContents dir

endsWith :: String -> String -> Bool
endsWith t s = t `elem` (tails s)

runHyLoRes :: Maybe NumWorkers -> FilePath -> IO Result
runHyLoRes wc f = HyLoRes.runWithParams clp
    where clp = defaultParams{filename    = Just f,
                              maxtimeout  = 30,
                              quietMode   = True,
                              workerCount = wc}


runExpecting :: Expected -> Maybe NumWorkers -> FilePath -> IO Bool
runExpecting exp_result wc file =
    do putStr $ concat ["(", maybe "serial" (\i -> "-n " ++ show i) wc, ") ",
                        file, "......... "]
       r <- runHyLoRes wc file
       case (r, exp_result) of
         (UNSAT, Unsat)  -> putStrLn "OK!" >> return True
         (UNSAT, Sat)    -> putStrLn "FAILED! (unsat)" >> return False
         (SAT m, Sat)    -> do b <- isASatisfyingModel (inducedModel m)
                               if b
                                 then do putStrLn "OK!"
                                         return True
                                 else do putStrLn "MODELCHECK FAILED"
                                         return False
         (SAT _, Unsat)  -> putStrLn "FAILED! (sat)" >> return False
         (INTERRUPTED,_) -> putStrLn "FAILED! (timeout)" >> return False
    --
    where isASatisfyingModel m =
            do fs <- parseOldFormat <$> readFile file
               --
               let ws = Set.toList (worlds m)
               --
               return $ any (\w -> and [(m,w) |= f | f <- fs]) ws
