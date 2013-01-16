module HyLoRes.Core.Serial ( runHyLoRes )

where

import Data.Foldable ( foldMap )
import Data.List ( sortBy )
import HyLoRes.Clause.BasicClause ( BasicClause )
import HyLoRes.Clause.SelFunction ( fromSelFuncString )
import HyLoRes.Clause ( size )

import HyLo.Signature ( getSignature )

import HyLoRes.Config               ( Params(..))
import HyLoRes.FrontEnd.CommandLine ( CmdLineParams(..), configureStats )

import HyLoRes.Statistics       ( StatsValues )
import HyLoRes.Core.Worker.Base ( Result(..) )

import qualified HyLoRes.ClauseSet as CS

import HyLoRes.Core.Worker         ( runSerial, postProcessNew, onClauseSet_ )
import HyLoRes.Core.GivenClauseAlg ( solve )

import HyLoRes.Util.Timeout ( TimeoutSignal )
import HyLoRes.Util ( compareUsing )

runHyLoRes :: [BasicClause]
           -> Params
           -> CmdLineParams
           -> TimeoutSignal
           -> IO (Result, [StatsValues])
runHyLoRes input_clauses params clp timeout_signal =
    do stats  <- configureStats clp
       result <- runSerial go params sel_fun stats timeout_signal
       return (result, [stats])
    --
    where input_sig = foldMap getSignature input_clauses
          sel_fun   = fromSelFuncString (selFuncStr clp)
          go        = do onClauseSet_ $ CS.addAllToNew (sortBy (compareUsing size) input_clauses )
                         postProcessNew
                         solve input_sig

