----------------------------------------------------
 --                                                --
-- HyLoRes.FrontEnd.PrettyPrint:                  --
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

module HyLoRes.FrontEnd.PrettyPrint (

    -- Print Functions for Resolution Rules
    logConsequentsForBinaryRule, logConsequentsForUnaryRule,

    -- Print stats
    printFinalStats,

    -- Print Given
    logGivenClause,

    -- Subsumption
    logPremiseSubsumption , logSubsumptions, logBwSubsumptions,

) where

import Prelude hiding ( log )

import HyLoRes.Formula ( At, Opaque )

import HyLoRes.Clause.BasicClause ( BasicClause )
import HyLoRes.Clause.FullClause ( FullClause, ClauseId, clauseId )

import HyLoRes.Statistics ( StatsValues, showAllMetrics )

import HyLoRes.Core.Rule.Metadata ( RuleId, Subsumption )

import HyLoRes.Logger ( MonadLogger, LoggerEvent(..), log )

import HyLoRes.Util ( separate )

logGivenClause :: MonadLogger m => FullClause (At f) -> m ()
logGivenClause cl = log L_Rules $ concat ["Given: ", show cl, "\n"]


-- Subsumption logging

logPremiseSubsumption :: MonadLogger m => FullClause f -> Subsumption -> m ()
logPremiseSubsumption cl s = log L_State $ concat ["Premise ",
                                                   show (clauseId cl),
                                                   " was subsumed!",
                                                   " (", show s, ")\n"]

logSubsumptions :: MonadLogger m => [FullClause (At Opaque)] -> m ()
logSubsumptions fcls = log L_State $ concatMap showSubsumption fcls
    where showSubsumption fcl = concat ["Clause ",
                                        show fcl,
                                        " was subsumed by the clause set!\n"]

logBwSubsumptions :: MonadLogger m
                  => FullClause (At Opaque)
                  -> [ClauseId]
                  -> m ()
logBwSubsumptions cl cls = log L_State $ concatMap showBwSubsumption cls
    where showBwSubsumption clId = concat ["Old clause ",
                                           show clId,
                                           " was subsumed by new clause ",
                                           show (clauseId cl),
                                           "!\n"]

-- Rule logging

binaryRuleHeader :: RuleId -> ClauseId -> ClauseId -> String
binaryRuleHeader ruleId mainPId sidePId =
    concat [show ruleId, " (by ", show mainPId, " and ", show sidePId, ") :"]

unaryRuleHeader :: RuleId -> ClauseId -> String
unaryRuleHeader ruleId mainPId =
    concat [show ruleId, " (by ", show mainPId, ") :"]

showConsequents :: [BasicClause] -> String
showConsequents [c] = show c
showConsequents cs  = concat ["{", lf_indent,
                              separate (',':lf_indent) $ map show cs,
                              lf_indent,
                              "}\n"]
    where lf_indent = "\n        "

logConsequentsForBinaryRule :: MonadLogger m
                            => RuleId
                            -> ClauseId
                            -> ClauseId
                            -> [BasicClause]
                            -> m ()
logConsequentsForBinaryRule ruleId mainPId sidePId cs =
    log L_Rules $ concat [binaryRuleHeader ruleId mainPId sidePId,
                          showConsequents cs]


logConsequentsForUnaryRule :: MonadLogger m
                           => RuleId
                           -> ClauseId
                           -> [BasicClause]
                           -> m ()
logConsequentsForUnaryRule ruleId mainPId cs  =
    log L_Rules $ concat [unaryRuleHeader ruleId mainPId,
                          showConsequents cs]


{- Printing Stats ---------------------------------}

printFinalStats :: [StatsValues] -> IO ()
printFinalStats =  mapM_ (\s -> showAllMetrics s >>= putStrLn)
