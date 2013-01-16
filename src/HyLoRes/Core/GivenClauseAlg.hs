----------------------------------------------------
--                                                --
-- HyLoRes.Core.Resolve:                          --
-- Implementation of the given clause algorithm   --
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

module HyLoRes.Core.GivenClauseAlg(solve) where

import Prelude hiding ( log )

import Control.Monad     ( when, liftM )
import Control.Monad.Fix ( fix )

import HyLoRes.Formula ( Signature, At, Nom, Opaque, label )
import qualified HyLoRes.Formula as F

import HyLoRes.Clause             ( size )
import HyLoRes.Clause.FullClause  ( FullClause,
                                    clauseId, distFormula, occursNom,
                                    specialize )
import HyLoRes.Formula.TypeLevel ( Spec(..) )

import qualified HyLoRes.ClauseSet as CS
import qualified HyLoRes.Subsumption.ClausesByFormulaIndex as CBI
import HyLoRes.ClauseSet.InUse ( allClausesIdx, unitEqIdx )

import HyLoRes.Core.Rule.Base ( Rule, Binary, Unary, Subsumption(..),
                                UnaRuleResult(..), BinRuleResult(..),
                                runUnaryRule, runParUnitRule,
                                runBinaryRule, mainPremises, sidePremises )

import HyLoRes.Core.Rule.Definitions ( resPropRule, resBoxRule,
                                       boxRule,     boxXRule,
                                       parEqRule,   parNeqRule,
                                       parPropRule, parNegPropRule,
                                       parBoxRule,  parRelRule,
                                       conjRule,    disjRule,
                                       diaRule,     downRule )

import qualified HyLoRes.Statistics as Stats

import HyLo.Util    ( sequenceUntil )
import HyLoRes.Util ( atLeastOne    )

import HyLoRes.Core.Worker.Base ( Result(..), Directive(..) )
import HyLoRes.Core.Worker      ( Worker,
                                  fromClauseSet, onClauseSet, onClauseSet_, onClausesIndex_,
                                  cycleCount, incCycleCount, param,
                                  getDirective, unsatDetected, postProcessNew )

import HyLoRes.ModelGen ( buildHerbrandModel )

import HyLoRes.Config ( actHybr, actModal )

import HyLoRes.FrontEnd.PrettyPrint ( logGivenClause, logPremiseSubsumption )
import HyLoRes.Logger               ( LoggerEvent(..), log )

type GivenClause f = FullClause f

type RuleMatcher t f = GivenClause f -> Worker t [RuleApp t]
type RuleApp     t   = Worker t RuleAppResult

data RuleAppResult = R{emptyClauseWasDerived  :: Bool,
                       givenClauseSubsumption :: Subsumption}
                deriving(Eq, Show)

noNeedToContinue :: RuleAppResult -> Bool
noNeedToContinue = atLeastOne emptyClauseWasDerived givenClauseWasSubsumed
    where givenClauseWasSubsumed = (None /=) . givenClauseSubsumption

withNoSidePremise :: Rule (Unary a) -> RuleMatcher t a
withNoSidePremise rule given = return [appUnary]
    where appUnary =
             do r <- runUnaryRule rule given
                return R{emptyClauseWasDerived  = emptyClauseWasDerivedU r,
                         givenClauseSubsumption = Semantic}

withGivenAsMain :: Rule (Binary (At a) (At b)) -> RuleMatcher t (At a)
withGivenAsMain rule given =
    do iu <- fromClauseSet CS.inUse
       let ss = sidePremises rule given iu
       --
       return . flip map ss $ \side ->
           do r <- runBinaryRule rule given side
              --
              when (sidePremiseSubsumption r /= None) $
                  disableSubsumedPremise (sidePremiseSubsumption r) side
              --
              return $ R{emptyClauseWasDerived  = emptyClauseWasDerivedB r,
                         givenClauseSubsumption = mainPremiseSubsumption r}

withGivenAsSide :: Rule (Binary (At a) (At b)) -> RuleMatcher t (At b)
withGivenAsSide rule given =
    do iu <- fromClauseSet CS.inUse
       let ms = mainPremises rule given iu
       --
       return . flip map ms $ \main ->
           do r <- runBinaryRule rule main given
              --
              when (mainPremiseSubsumption r /= None) $
                  disableSubsumedPremise (mainPremiseSubsumption r) main
              --
              return R{emptyClauseWasDerived  = emptyClauseWasDerivedB r,
                       givenClauseSubsumption = sidePremiseSubsumption r}

-- par-unit with given as side premise
parUnitS :: RuleMatcher t (At Nom)
parUnitS given =
    do let i  = label $ distFormula given
       --
       all_clauses <- fromClauseSet CS.getAllFullClauses
       --
       -- Apply parUnit to every clause containing the reducing nominal.
       -- IMPORTANT: The given clause must be kept after this. There are
       -- three reasons for this:
       --  a) if the label is an skolem nom, it may be generated again!
       --  b) due to the side-conditions of the par rule, the replacing
       --     nominal might not disappear completely (it may occur in
       --     another unit-equality in clauses)
       --  c) if the formula turns out to be satisfiable, we still need
       --     this equality in order to build a proper herbrand model
       return $ [parUnitAppS c given | c <- all_clauses,
                                       occursNom i c,
                                       --
                                       safeToApplyParUnit c given]
    --
    where parUnitAppS c d =
              do r <- runParUnitRule c d
                 --
                 disableSubsumedPremise ByParUnit c
                 --
                 return R{emptyClauseWasDerived  = emptyClauseWasDerivedB r,
                          givenClauseSubsumption = None}

-- par-unit with given as main
parUnitM :: RuleMatcher t (At f)
parUnitM given =
    do iu <- fromClauseSet CS.inUse
       return $ [parUnitAppM given c | c <- allClausesIdx (unitEqIdx iu),
                                       let eq = distFormula c,
                                       occursNom (label eq) given,
                                       safeToApplyParUnit given c]
    --
    where parUnitAppM c d =
              do r <- runParUnitRule c d
                 --
                 return R{emptyClauseWasDerived  = emptyClauseWasDerivedB r,
                          givenClauseSubsumption = ByParUnit}

safeToApplyParUnit :: FullClause (At f) -> FullClause (At Nom) -> Bool
safeToApplyParUnit main side = case specialize main_f of
                                   AtNom main_eq -> let i  = label main_f
                                                        i' = label side_f
                                                    in  size main > 1  || -- (a)
                                                        (i /= i')      || -- (b)
                                                        main_eq > side_f
                                   _             -> True
                                 -- when the main premise is a unit equality
                                 -- such that it could be also used to
                                 -- rewrite the side clause, we must
                                 -- be careful to check the main premise
                                 -- to be larger (i.e. to observe the side
                                 -- condition of the  par-@ rule).
                                 -- if this is not done, the label of the side
                                 -- might end-up vanishing from the clause set,
                                 -- compromising completeness.
                                 -- observe that if condition (b) above
                                 -- is true then, either i' matches the target
                                 -- nom of main_f and, thus, main > side,
                                 -- or else i only occurs inside a tonom
                                 -- and should be replaced too.
    --
    where main_f = distFormula main
          side_f = distFormula side

noApp :: RuleMatcher t a
noApp = \_     -> return []

inOrder :: [RuleMatcher t a] -> RuleMatcher t a
inOrder fs    = \given -> concat `liftM` sequence [f given | f <- fs]

onlyIf :: RuleMatcher t a -> Bool-> RuleMatcher t a
f `onlyIf` b = if b then f else noApp

{-
cond :: (GivenClause a -> Bool)
     -> RuleMatcher t a
     -> RuleMatcher t a
     -> RuleMatcher t a
cond p a b = \c -> if p c then a c else b c
-}

mkRuleMatcher :: Bool -> Bool -> RuleMatcher t (At f)
mkRuleMatcher modal hybr = \given ->
    case specialize given of
        AtNom c -> (if size c == 1
                   then inOrder [ parUnitM, parUnitS]
                   else inOrder [ parUnitM,
                                 (parNeqRule     `withGivenAsSide`),
                                 (parEqRule      `withGivenAsMain`),
                                 (parEqRule      `withGivenAsSide`),
                                 (parPropRule    `withGivenAsSide`),
                                 (parNegPropRule `withGivenAsSide`),
                                 (parBoxRule     `withGivenAsSide`) `onlyIf` modal,
                                 (parRelRule     `withGivenAsSide`) `onlyIf` modal]) c
        --
        AtNegNom c  -> inOrder [ parUnitM,
                                (parNeqRule `withGivenAsMain`)] c
        --
        AtProp c    -> inOrder [ parUnitM,
                                (resPropRule `withGivenAsSide`),
                                (parPropRule `withGivenAsMain`) `onlyIf` hybr] c
        --
        AtNegProp c -> inOrder [ parUnitM,
                                (resPropRule    `withGivenAsMain`),
                                (parNegPropRule `withGivenAsMain`) `onlyIf` hybr] c
        --
        AtDiamNom c -> inOrder [ parUnitM,
                                (boxRule    `withGivenAsSide`),
                                (boxXRule   `withGivenAsSide`), -- onlyIf hasPast
                                (parRelRule `withGivenAsMain`) `onlyIf` hybr] c
        --
        AtDiamF c   -> inOrder [ parUnitM,
                                (resBoxRule `withGivenAsSide`),
                                (diaRule    `withNoSidePremise`)] c
        --
        AtBoxF c    -> inOrder [ parUnitM,
                                (boxRule    `withGivenAsMain`),
                                (boxXRule   `withGivenAsMain`), -- onlyIf hasPast
                                (parBoxRule `withGivenAsMain`)] c
        --
        AtConj c    -> inOrder [ parUnitM,
                                (conjRule `withNoSidePremise`)] c
        --
        AtDisj c    -> inOrder [ parUnitM,
                                (disjRule `withNoSidePremise`)] c
        --
        AtDownF c   -> inOrder [ parUnitM,
                                (downRule `withNoSidePremise`)] c
        --
        AtTop{}     -> return [return R{emptyClauseWasDerived  = False,
                                        givenClauseSubsumption = Semantic}]
        --
        AtNegTop{}  -> error "Given clause contains a false formula!"


disableSubsumedPremise :: Subsumption -> FullClause (At f) -> Worker t ()
disableSubsumedPremise s c =
    do logPremiseSubsumption c s
       Stats.recordSubsumedPremise
       --
       onClauseSet_ $ case s of
         IsSubset  -> CS.removeFromInUse c
         Semantic  -> CS.removeFromInUse c
         ByParUnit -> \cs -> fst (CS.removeClauseById (clauseId c) cs)
         None      -> fail "disableSubsumedPremise: subsumption == None??"
       onClausesIndex_ $  (CBI.removeFromIndex c)

{- selectGiven: Given

Return "the best" clause in Clauses, given the complexity criterium.
Once every 6 cycles, it choses the oldest formula from Clauses, so
that formulas are not delayed for ever.
-}
selectGiven :: Worker t (FullClause (At Opaque))
selectGiven =
    do count <- cycleCount
       incCycleCount
       --
       given_clause <- onClauseSet $ if (count `mod` 6 == 0)
                                       then CS.oldestInClauses
                                       else CS.minInClauses
       --
       logGivenClause given_clause
       Stats.recordGivenClause given_clause
       --
       return given_clause

logState :: Worker t ()
logState = do showCS <- fromClauseSet show
              log L_State $ unlines ["---------------",
                                     showCS,
                                     "---------------"]
              Stats.logInspectionMetrics


{----------------------------------------------------------------------}
{- Here begins the main loop ------------------------------------------}
{----------------------------------------------------------------------}

{- solve:

   Determines the rules needed and saturates the clauses set.
   The signature is required to build a proper Herbrand model
-}
solve :: Signature -> Worker t Result
solve sig =
    do modal <- param actModal
       hybr  <- param actHybr
       let rulesFor = mkRuleMatcher modal hybr
       --
       fix $ \tryNext ->
         do action <- getDirective
            case action of
              Abort        -> return INTERRUPTED
              --
              Exhausted    -> do iu <- fromClauseSet $ CS.inUse
                                 return $ SAT (buildHerbrandModel sig iu)
              --
              AllSubsumed  ->
                  do
                    --
                    logState
                    --
                    postProcessNew
                    tryNext
              --
              Continue new ->
                  do -- Continue implies that either Clauses or
                     -- new is not empty
                     --
                    onClauseSet_ $ CS.addAllToClauses new
                    Stats.recordQueuedClauses new
                    --
                    logState
                    --
                    given_cl <- selectGiven
                    --
                    rule_apps <- rulesFor given_cl
                    --
                    -- TODO: If given was subsumed, then we should rollback
                    -- all rule applications and replay only the last one!
                    rs <- sequenceUntil noNeedToContinue rule_apps
                    let last_res = last rs
                    case (null rs,
                          emptyClauseWasDerived  last_res,
                          givenClauseSubsumption last_res) of
                      (True,_,_) -> do onClauseSet_ $ CS.addToInUse given_cl
                                       postProcessNew
                                       tryNext
                      --
                      (_,True,_) -> do unsatDetected
                                       return UNSAT
                      --
                      (_,_,None) -> do onClauseSet_ $ CS.addToInUse given_cl
                                       postProcessNew
                                       tryNext
                      --
                      (_,_,subs) -> do logPremiseSubsumption given_cl subs
                                       Stats.recordSubsumedPremise
                                       postProcessNew
			 	       onClausesIndex_ (CBI.removeFromIndex given_cl)
                                       tryNext
