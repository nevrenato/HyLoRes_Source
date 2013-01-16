----------------------------------------------------
--                                                --
-- HyLoRes:                                       --
-- Main function, checks command line options     --
-- calls the parser and then runs the solver on   --
-- the input.  The file also includes the timing  --
-- routines.                                      --
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

module HyLoRes.Main ( runWithParams )

where

import System.IO          ( hSetBuffering, stdin, BufferMode(LineBuffering) )
import System.CPUTime     ( getCPUTime )

import qualified Data.Foldable as F

import Control.Monad       ( unless )
import Control.Applicative ( (<$>) )

import HyLo.InputFile ( parseOldFormat )

import HyLoRes.Util ( commaSeparateHdr )

import HyLoRes.Clause ( Clause(isEmpty) )

import HyLoRes.Clause.BasicClause ( singletonClause )

import HyLoRes.Formula                 ( nnfAtFormula )
import HyLoRes.Formula.Transformations ( fromSimpleSig, embedUnivMod )

import HyLo.Signature.Simple ( NomSymbol(X) )
import HyLo.Signature   ( getSignature, nomSymbols, delNomFromSig )
import HyLoRes.ModelGen ( inducedModel, expand )

import HyLoRes.Config ( Params(..) )

import HyLoRes.Core.Worker.Base ( Result(..) )

import qualified HyLoRes.Core.SMP    as SMP
import qualified HyLoRes.Core.Serial as Ser

import HyLoRes.FrontEnd.PrettyPrint ( printFinalStats )

import HyLoRes.FrontEnd.CommandLine ( CmdLineParams(..) )

import HyLoRes.Util.Timeout ( withNoTimeout, notifyOnTimeout )

import HyLoRes.Logger ( LoggerCfg(..) )

runWithParams :: CmdLineParams -> IO Result
runWithParams clp =
    do start <- getCPUTime
       --
       let myPutStrLn = if quietMode clp then const (return ()) else putStrLn
       --
       let fromStdIn = do myPutStrLn $ "Reading from stdin (run again with" ++
                                       "`--help' for usage options)"
                          hSetBuffering stdin LineBuffering
                          getContents
       fs  <- parseOldFormat <$> maybe fromStdIn readFile (filename clp)
       --
       let sig = F.foldMap getSignature fs
       --
       let inputClauses = map (singletonClause . nnfAtFormula) .
                          embedUnivMod                         .
                          map fromSimpleSig $ fs
       --
       fs `seq` do myPutStrLn "\nInput:"
                   myPutStrLn  $ commaSeparateHdr "   " inputClauses
                   myPutStrLn "End of input\n"
       --
       if any isEmpty inputClauses
         then do myPutStrLn "The formula is unsatisfiable\nClauses generated: 0"
                 return UNSAT
         else do let params  = P{loggerCfg  = LoggerCfg{
                                              logState = mustLogState clp,
                                              logRules = mustLogRules clp,
                                              logComm  = mustLogComm  clp
                                              },
                                 clausesOrd = complexityStr clp,
                                 timeoutVal = maxtimeout clp,
                                 bwSubsIsOn = useBWSubs clp,
                                 actModal   = True, -- TODO: FIXME
                                 actHybr    = True  -- FIXME
                                                    -- (must test for
                                                    --  input nominals or
                                                    --  state variables)
                                }
                 let run = maybe Ser.runHyLoRes SMP.runHyLoRes $ (workerCount clp)
                 let handleTimeout
                      | (maxtimeout clp) > 0 = notifyOnTimeout (maxtimeout clp)
                      | otherwise            = withNoTimeout
                 --
                 (result, stats) <- handleTimeout (run inputClauses params clp)
                 --
                 r <- case result of
                         (SAT m)      ->
                           do myPutStrLn "The formula is satisfiable"
                              -- HACK
                              -- the herbrand model is expanded to the
                              -- signature of the initial formulas, to
                              -- account for nominals that dissappeared
                              -- during conversion to NNF (e.g. N2:N1:P1)
                              let m' = expand (delVars sig) m
                              saveGenModel m'
                              return (SAT m')

                         UNSAT        ->
                           do myPutStrLn "The formula is unsatisfiable"
                              return UNSAT

                         INTERRUPTED  ->
                           do myPutStrLn "Timeout reached."
                              return INTERRUPTED
                 --
                 unless ( quietMode clp ) $ printFinalStats  stats
                 --
                 end <- getCPUTime
                 let elapsed_time = fromInteger (end - start) / 1000000000000.0
                 myPutStrLn $ "Elapsed time: " ++ show (elapsed_time :: Double)
                 --
                 return r

    --
    where saveGenModel m = maybe (return ()) doWrite (genModel clp)
              where doWrite f = do writeFile f (show $ inducedModel m)
                                   unless ( quietMode clp ) $
                                          putStrLn $ "Model saved as " ++ f
          --
          isVar (X _) = True
          isVar _     = False
          delVars s = F.foldr (\n f -> delNomFromSig n . f) id noms $ s
            where noms = filter isVar . F.toList $ nomSymbols s

