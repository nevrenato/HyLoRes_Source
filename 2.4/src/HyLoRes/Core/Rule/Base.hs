{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
----------------------------------------------------
--                                                --
-- HyLoRes.Core.Rule.Base:                        --
-- The implementation of all the rules of the     --
-- calculus                                       --
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
module HyLoRes.Core.Rule.Base (

    -- Rule type
    Rule(..), Unary, Binary,

    -- Premise types
    MainPremise, MainPremiseF, SidePremise, SidePremiseF,

    -- Rule results
    BinRuleResult(..),
    UnaRuleResult(..),
    Subsumption(..), iff,

    ruleId,
    runB, runBinaryRule, mainPremises,sidePremises,
    runU, runUnaryRule,
    runParUnitRule
)

where

import HyLoRes.Core.Rule.Metadata ( RuleId(..), Subsumption(..) )

import HyLoRes.Formula    ( Formula, At, Nom, killNom, flatten )
import HyLoRes.Formula.NF ( fromNF )

import HyLoRes.Clause             ( isEmpty, toFormulaList )
import HyLoRes.Clause.BasicClause ( BasicClause, add, fromList )
import HyLoRes.Clause.FullClause  ( FullClause, clauseId,
                                    splitAtDist, distFormula )

import HyLoRes.ClauseSet       ( addAllToNew )
import HyLoRes.ClauseSet.InUse ( InUseClauseSet )

import qualified HyLoRes.Statistics as Stats ( recordFiredRule )

import HyLoRes.FrontEnd.PrettyPrint ( logConsequentsForBinaryRule,
                                      logConsequentsForUnaryRule )

import HyLoRes.Core.Worker ( Worker, onClauseSet_ )

type MainPremise  f = FullClause f
type MainPremiseF f = (Formula f, BasicClause)

type SidePremise  f = FullClause f
type SidePremiseF f = (Formula f, BasicClause)

type Consequent     = BasicClause

data Unary  main
data Binary main side

iff :: Subsumption -> Bool -> Subsumption
iff s b = if b then s else None

data Rule t where
    UnaryRule  :: RuleId
               -> (MainPremiseF (At f) -> UnaRuleResult)
               -> Rule (Unary (At f))
    BinRule :: RuleId
               -> (MainPremiseF (At f) -> SidePremiseF (At g) -> BinRuleResult)
               -> (Formula (At f) -> InUseClauseSet -> [SidePremise (At g)])
               -> (Formula (At g) -> InUseClauseSet -> [MainPremise (At f)])
               -> Rule (Binary (At f) (At g))

data UnaRuleResult = UR{consequentsU           :: [Consequent],
                        emptyClauseWasDerivedU :: Bool}

data BinRuleResult = BR{consequentsB           :: [Consequent],
                        mainPremiseSubsumption :: Subsumption,
                        sidePremiseSubsumption :: Subsumption,
                        emptyClauseWasDerivedB :: Bool}

ruleId :: Rule t -> RuleId
ruleId (UnaryRule r  _)  = r
ruleId (BinRule r _ _ _) = r


runUnaryRule :: Rule (Unary a) -> MainPremise a -> Worker t UnaRuleResult
runUnaryRule r main =
    do let main_split  = splitAtDist main
           --
           result      = runU r main_split
           consequents = consequentsU result
           --
           rule_id     = ruleId r
       --
       onClauseSet_ $ addAllToNew consequents
       --
       Stats.recordFiredRule rule_id consequents
       logConsequentsForUnaryRule rule_id (clauseId main) consequents
       --
       return result

runU :: Rule (Unary a) -> MainPremiseF a -> UnaRuleResult
runU (UnaryRule _ f) = f


runBinaryRule :: Rule (Binary a b)
              -> MainPremise a
              -> SidePremise b
              -> Worker t BinRuleResult
runBinaryRule r main side =
    do let main_split  = splitAtDist main
           side_split  = splitAtDist side
           --
           result      = runB r main_split side_split
           consequents = consequentsB result
           --
           rule_id     = ruleId r
       --
       onClauseSet_ $ addAllToNew consequents
       --
       Stats.recordFiredRule rule_id consequents
       logConsequentsForBinaryRule rule_id
                                   (clauseId main)
                                   (clauseId side)
                                   consequents
       --
       return result

runB :: Rule (Binary a b) -> MainPremiseF a -> SidePremiseF b -> BinRuleResult
runB (BinRule _ f _ _) = f

sidePremises :: Rule (Binary a b)
             -> MainPremise a
             -> InUseClauseSet
             -> [SidePremise b]
sidePremises (BinRule _ _ g _) = g . distFormula

mainPremises :: Rule (Binary a b)
             -> SidePremise b
             -> InUseClauseSet
             -> [MainPremise a]
mainPremises (BinRule _ _ _ g) = g . distFormula

runParUnitRule :: MainPremise (At f)
               -> SidePremise (At Nom)
               -> Worker t BinRuleResult
runParUnitRule = runBinaryRule $ BinRule R_ParUnit par_unit void void
    where void = undefined


{----------- Paramodulation against a unit equality clause -----------}


par_unit :: MainPremiseF (At f) -> SidePremiseF (At Nom) -> BinRuleResult

par_unit          (mainF, c)   (sideF, _)   = -- ({sideF,_} is singleton,
                ----------------------------  --  label(sideF) occurs {mainF,c},
 let consequent = doPar mainF `add` doPar_c   --  if {mainF,_} is singleton
     --                                             mainF > sideF
     doPar_c = fromList [doPar (fromNF f) | f <- toFormulaList c]
     --
     -- killNom will remove all traces of the nominal
     -- (even those inside toNom will be replaced)
     doPar = uncurry killNom (flatten sideF)
 in
     BR{consequentsB = [consequent],
        mainPremiseSubsumption = ByParUnit,
        sidePremiseSubsumption = None,
        emptyClauseWasDerivedB = isEmpty consequent}
