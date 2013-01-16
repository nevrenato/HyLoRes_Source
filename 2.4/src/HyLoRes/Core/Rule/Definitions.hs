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
module HyLoRes.Core.Rule.Definitions (
    -- Rules
    resPropRule, resBoxRule,
    -- observe there's no need for a resNomRule
    -- since it's just a case of the parNeqRule
    --
    boxRule, boxXRule,
    --
    diaRule, downRule,
    disjRule, conjRule,
    --
    parPropRule, parNegPropRule,
    parBoxRule, parRelRule,
    parEqRule, parNeqRule,
    --
    unit_tests
)

where

import qualified Test.QuickCheck as QC ( label )
import Test.QuickCheck ( Property, Testable, forAll, (==>), arbitrary )
import HyLo.Test       ( UnitTest, TestCase, runTest, runTestWith,
                         Config(..), defaultConfig )

import HyLoRes.Formula ( Formula, NomSym, RelSym,
                         At, Nom, Prop, Neg, Diam, Disj, Conj, Box, Down,
                         Opaque,
                         at, nom, neg, diam, opaque, onSubf, box,
                         replaceNom, instanceFreeVar,
                         label, boundVar, subf, subfs, flatten,
                         symbol, relSym, invRel,
                         isSkolemNom, toNom, onInvToNom )

import HyLoRes.Formula.Util ( isTrivFalse )

import HyLoRes.Clause             ( Clause(..) )
import HyLoRes.Clause.BasicClause ( BasicClause, union, add, delete, fromList,
                                    isTrivTaut )
import HyLoRes.Clause.FullClause  ( FullClause, distFormula )

import HyLoRes.ClauseSet.InUse ( InUseClauseSet,
                                 clauses, clausesByNom,
                                 nonUnitEqIdx, atNegNomIdx,
                                 atPropIdx,    atNegPropIdx,
                                 atDiaNomIdx,  atDiaNomRevIdx,
                                 atBoxFIdx )

import HyLoRes.Core.Rule.Base
import HyLoRes.Core.Rule.Metadata ( RuleId(..) )

import HyLo.Model     ( (|=), modelFor )
import HyLo.Signature ( getSignature, hasInv )

targetNomR :: Formula (At (Diam Nom)) -> NomSym
targetNomR = symbol . subf . subf


{-------- The resolution rule -----------------}

res :: MainPremiseF (At a) -> SidePremiseF (At b) -> BinRuleResult

res             (_, c)     (_, d)      =
              -----------------------
 let resolvent =  c `union` d
 in
     BR{consequentsB           = [resolvent],
        mainPremiseSubsumption = IsSubset `iff` (d `subsetEq` c),
        sidePremiseSubsumption = IsSubset `iff` (c `subsetEq` d),
        emptyClauseWasDerivedB = isEmpty resolvent}


resPropRule ::Rule (Binary (At (Neg Prop)) (At Prop))
resPropRule = BinRule R_ResP
                      res
                      (\mainF -> uncurry clauses (flatten mainF) . atPropIdx)
                      (\sideF -> uncurry clauses (flatten sideF) . atNegPropIdx)


resBoxRule :: Rule (Binary (At (Box Opaque)) (At (Diam a)))
resBoxRule = BinRule R_ResB
                     res
                     (\_     -> const [])
                     (\sideF -> let negB  = neg . onSubf (onSubf opaque)
                                    (i,r) = (label sideF,
                                             relSym . subf $ sideF)
                                in filter (((negB sideF) ==) . distFormula) .
                                   clauses i r . atBoxFIdx)


{---------- The BOX (elimination) rules ------------}

boxUsing :: (Formula (At (Diam Nom)) -> NomSym)
         -> MainPremiseF (At (Box Opaque))
         -> SidePremiseF (At (Diam Nom))
         -> BinRuleResult
boxUsing f          (mainF, c) (sideF, d)     =
                 ----------------------------
 let consequent =   newF `add` (c `union` d)
     --
     newF       = at (f sideF) (subf . subf $ mainF)
 in
     BR{consequentsB            = [consequent],
        mainPremiseSubsumption = IsSubset `iff` (c `contains` newF &&
                                                 d `subsetEq` c),
        sidePremiseSubsumption = IsSubset `iff` (d `contains` newF &&
                                                 c `subsetEq` d),
        emptyClauseWasDerivedB = isEmpty c && isEmpty d && isTrivFalse newF}


boxRule :: Rule (Binary (At (Box Opaque)) (At (Diam Nom)))
boxRule = BinRule R_Box
                  (boxUsing targetNomR)
                  (\mainF -> clauses (label mainF) (relSym . subf $ mainF) .
                             atDiaNomIdx)
                  (\sideF -> clauses (label sideF) (relSym . subf $ sideF) .
                             atBoxFIdx)

boxXRule :: Rule (Binary (At (Box Opaque)) (At (Diam Nom)))
boxXRule = BinRule R_BoxX
                   (boxUsing label)
                   (\mainF -> maybe (const [])
                                    (\invR -> clauses (label mainF) invR)
                                    (invRel . relSym . subf $ mainF) .
                              atDiaNomRevIdx)


                   (\sideF -> maybe (const [])
                                    (\invR -> clauses (targetNomR sideF) invR)
                                    (invRel . relSym . subf $ sideF) .
                              atBoxFIdx)


{------------- The rule for splitting diamonds -----------}

dia :: MainPremiseF (At (Diam Opaque)) -> UnaRuleResult

dia                 (mainF, c)    =
                 ----------------
 let conseq1 =    newRel `add` c
     conseq2 =    atF    `add` c
     --
     newRel  = onSubf (onSubf (\_ -> nom j)) mainF
     atF     = at j (subf . subf $ mainF)
     --
     j       = toNom mainF
 in
    UR{consequentsU           = [conseq1, conseq2],
       emptyClauseWasDerivedU = isEmpty c && isTrivFalse atF}


diaRule :: Rule (Unary (At (Diam Opaque)))
diaRule = UnaryRule R_Dia dia


{------------- The rule for removing downarrows -----------}

down :: MainPremiseF (At (Down Opaque)) -> UnaRuleResult
down                (mainF, c)    =
                  -------------
 let consequent = newF `add` c
     --
     newF = doReplacement `onSubf` mainF
     doReplacement f = instanceFreeVar (boundVar f) (label mainF) (subf f)
     --
 in UR{consequentsU           = [consequent],
       emptyClauseWasDerivedU = isEmpty consequent}


downRule :: Rule (Unary (At (Down Opaque)))
downRule = UnaryRule R_Down down



{------------- The rule for disjunctions ------------}

disj :: MainPremiseF (At Disj) -> UnaRuleResult

disj                  (mainF, c)    =
                   ---------------
 let consequent =  newFs `union` c
     --
     newFs = fromList [at (label mainF) f | f <- subfs (subf mainF)]
 in
     UR{consequentsU           = [consequent],
        emptyClauseWasDerivedU = isEmpty consequent}


disjRule :: Rule (Unary (At Disj))
disjRule = UnaryRule R_Disj disj


{------------- The rule for conjunctions ------------}

conj :: MainPremiseF (At Conj) -> UnaRuleResult

conj                  (mainF, c)    =
                   ------------------
 let consequents =  [at i f `add` c | f <- subfs (subf mainF)]
     --
     i = label mainF
 in
     UR{consequentsU           = consequents,
        emptyClauseWasDerivedU = isEmpty c && any isEmpty consequents}


conjRule :: Rule (Unary (At Conj))
conjRule = UnaryRule R_Conj conj

{- =============== Paramodulation rules begin here ============== -}

targetNomE :: Formula (At Nom) -> NomSym
targetNomE = symbol . subf


{----------- Paramodulation on the labels of propositions -------------}

-- par_p: Labelled paramodulation on labels,
--        no contradiction can be derived
par_p :: MainPremiseF (At f) -> SidePremiseF (At Nom) -> BinRuleResult

par_p                (mainF, c)   (sideF, d)     =
                   ---------------------------
 let consequent =    newF `add` (c `union` d)
     --
     newF = at (targetNomE sideF)  (subf mainF)
 in
     BR{consequentsB = [consequent],
        mainPremiseSubsumption = Semantic `iff` (d `subsetEq` c),
        sidePremiseSubsumption = None,
        emptyClauseWasDerivedB = False }


parPropRule ::Rule (Binary (At Prop) (At Nom))
parPropRule = BinRule R_ParP
                      par_p
                      (\mainF -> clausesByNom (label mainF) . nonUnitEqIdx)
                      (\sideF -> clausesByNom (label sideF) . atPropIdx)

parNegPropRule :: Rule (Binary (At (Neg Prop)) (At Nom))
parNegPropRule = BinRule R_ParNegP
                         par_p
                         (\mainF -> clausesByNom (label mainF) .
                                    nonUnitEqIdx)
                         (\sideF -> clausesByNom (label sideF) .
                                    atNegPropIdx)


{------------------------- Paramodulation on boxes  --------------------------}
{----- (only labels are matched, but all the occurrences are replaced) -------}

par_b :: MainPremiseF (At (Box Opaque))
      -> SidePremiseF (At Nom)
      -> BinRuleResult

par_b                (mainF, c)   (sideF, d)     =
                   ---------------------------
 let consequent =    newF `add` (c `union` d)
     --
     newF = replaceNom (label sideF) (targetNomE sideF) mainF
 in
     BR{consequentsB           = [consequent],
        mainPremiseSubsumption = Semantic `iff` (d `subsetEq` c),
        sidePremiseSubsumption = None,
        emptyClauseWasDerivedB = False}


parBoxRule :: Rule (Binary (At (Box Opaque)) (At Nom))
parBoxRule = BinRule R_ParB
                     par_b
                     (\mainF -> clausesByNom (label mainF) . nonUnitEqIdx)
                     (\sideF -> clausesByNom (label sideF) . atBoxFIdx)


{------------ Labelled paramodulation on equalities ------------}

par_eq :: MainPremiseF (At Nom) -> SidePremiseF (At Nom) -> BinRuleResult

par_eq              (mainF, c) (sideF, d)         =
                  ----------------------------   (mainF > sideF)
 let consequent =   newF `add` (c `union` d)
     --
     newF = at i (subf mainF)
     --
     i = targetNomE sideF
 in
    BR{consequentsB           = [consequent],
                                -- it makes sense to make this distinction
                                -- only for the paramodulation of equalities
       mainPremiseSubsumption = case (d `subsetEq` c, c `contains` newF) of
                                  (True, False) -> Semantic
                                  (True, True)  -> IsSubset
                                  _             -> None,
       sidePremiseSubsumption = IsSubset `iff` (d `contains` newF &&
                                                c `subsetEq` d),
       emptyClauseWasDerivedB = False}


parEqRule :: Rule (Binary (At Nom) (At Nom))
parEqRule =
    BinRule R_ParEq
            par_eq
            (\mainF iu ->
                 [c | c <- clausesByNom (label mainF) . nonUnitEqIdx $ iu,
                      mainF > distFormula c])
            (\sideF iu ->
                 [c | c <- clausesByNom (label sideF) . nonUnitEqIdx $ iu,
                      distFormula c > sideF])

{------------ Labelled paramodulation on inequalities ------------}

par_neq :: MainPremiseF (At (Neg Nom)) -> SidePremiseF (At Nom) -> BinRuleResult

par_neq            (mainF, c)   (sideF, d)     =
                  ---------------------------
 let consequent =   newF `add` (c `union` d)
     --
     newF = at i (subf mainF)
     --
     i = targetNomE sideF
 in
    BR{consequentsB           = [consequent],
       mainPremiseSubsumption = Semantic `iff` (d `subsetEq` c),
       sidePremiseSubsumption = IsSubset `iff` (isTrivFalse newF &&
                                                c `subsetEq` d),
       emptyClauseWasDerivedB = isEmpty consequent}

parNeqRule :: Rule (Binary (At (Neg Nom)) (At Nom))
parNeqRule = BinRule R_ParNeq
                     par_neq
                     (\mainF -> clausesByNom (label mainF) . nonUnitEqIdx)
                     (\sideF -> clausesByNom (label sideF) . atNegNomIdx)


{-------- Labelled paramodulation on relations ------}

par_rel_1 :: MainPremiseF (At (Diam Nom))
          -> SidePremiseF (At Nom)
          -> BinRuleResult
par_rel_1             (mainF, c)   (sideF, d)      =
                    --------------------------- (level(target (mainF)) > 0)
 let consequent1 =   newRel `add` c_union_d
     consequent2 =   newEq  `add` c_union_d
     --
     c_union_d = c `union` d
     --
     newRel = at i (diam r $ nom l)
     newEq  = at k (nom l)
     --
     (_,r,k) = flatten mainF
     (_,  i) = flatten sideF
     --
     Just l = onInvToNom k (\atj_diam_f -> toNom $ at i (subf atj_diam_f))
 in
    BR{consequentsB           = [consequent1, consequent2],
       mainPremiseSubsumption = Semantic `iff` (d `subsetEq` c),
       sidePremiseSubsumption = IsSubset `iff` (d `contains` newEq &&
                                                c `subsetEq` d),
       emptyClauseWasDerivedB = False}


par_rel_2 :: MainPremiseF (At (Diam Nom))
          -> SidePremiseF (At Nom)
          -> BinRuleResult
par_rel_2             (mainF, c)   (sideF, d)      =
                    --------------------------- (level(target (mainF)) = 0)
 let consequent =     newF `add` (c `union` d)
     --
     newF = replaceNom i j mainF
     --
     (i,j) = flatten sideF
 in
     BR{consequentsB           = [consequent],
        mainPremiseSubsumption = Semantic `iff` (d `subsetEq` c),
        sidePremiseSubsumption = None,
        emptyClauseWasDerivedB = False
     }

parRelRule :: Rule (Binary (At (Diam Nom)) (At Nom))
parRelRule = BinRule R_ParR
                     (\(mainF,c) -> if not . isSkolemNom . targetNomR $ mainF
                                      then par_rel_2 (mainF, c)
                                      else par_rel_1 (mainF, c))
                     (\mainF -> clausesByNom (label mainF) . nonUnitEqIdx)
                     (\sideF -> clausesByNom (label sideF) . atDiaNomIdx)


-- --------------------
-- QuickCheck stuff
-- --------------------

prop_isSound_resP  :: NomSym
                   -> Formula Prop
                   -> BasicClause
                   -> BasicClause
                   -> Property
prop_isSound_resP i p c d = testSoundnessBin main side (runB resPropRule)
    where main = (at i $ neg p, c)
          side = (at i p, d)

prop_subsIsSound_resP :: NomSym
                      -> Formula Prop
                      -> BasicClause
                      -> BasicClause
                      -> Property
prop_subsIsSound_resP i p c d = testSubsBin main side (runB resPropRule)
    where main = (at i $ neg p, c)
          side = (at i p, d)

prop_emptyness_resP :: NomSym
                    -> Formula Prop
                    -> BasicClause
                    -> BasicClause
                    -> Bool
prop_emptyness_resP i p c d = testEmptynessBin main side (runB resPropRule)
    where main = (at i $ neg p, c)
          side = (at i p, d)


prop_isSound_resB :: NomSym
                  -> RelSym
                  -> Formula Opaque
                  -> BasicClause
                  -> BasicClause
                  -> Property
prop_isSound_resB i r f c d = testSoundnessBin main side (runB resBoxRule)
    where main = (at i $ box r f, c)
          side = (at i $ diam r (neg f), d)

prop_subsIsSound_resB :: NomSym
                      -> RelSym
                      -> Formula Opaque
                      -> BasicClause
                      -> BasicClause
                      -> Property
prop_subsIsSound_resB i r f c d = testSubsBin main side (runB resBoxRule)
    where main = (at i $ box r f, c)
          side = (at i $ diam r (neg f), d)


prop_emptyness_resB :: NomSym
                    -> RelSym
                    -> Formula Opaque
                    -> BasicClause
                    -> BasicClause
                    -> Bool
prop_emptyness_resB i r f c d = testEmptynessBin main side (runB resBoxRule)
    where main = (at i $ box r f, c)
          side = (at i $ diam r (neg f), d)


prop_isSound_box :: NomSym
                 -> RelSym
                 -> (Formula Opaque, BasicClause)
                 -> (Formula Nom, BasicClause)
                 -> Property
prop_isSound_box i r (a,c) (j,d) = testSoundnessBin main side (runB boxRule)
    where main = (at i $ box r a, c)
          side = (at i $ diam r j, d)

prop_subsIsSound_box :: NomSym
                     -> RelSym
                     -> (Formula Opaque, BasicClause)
                     -> (Formula Nom, BasicClause)
                     -> Property
prop_subsIsSound_box i r (a,c) (j,d) = testSubsBin main side (runB boxRule)
    where main = (at i $ box r a, c)
          side = (at i $ diam r j, d)

prop_emptyness_box :: NomSym
                   -> RelSym
                   -> (Formula Opaque, BasicClause)
                   -> (Formula Nom, BasicClause)
                   -> Bool
prop_emptyness_box i r (a,c) (j,d) = testEmptynessBin main side (runB boxRule)
    where main = (at i $ box r a, c)
          side = (at i $ diam r j, d)


prop_isSound_boxX :: NomSym
                  -> RelSym
                  -> (Formula Opaque, BasicClause)
                  -> (NomSym, BasicClause)
                  -> Property
prop_isSound_boxX i r (a,c) (j,d) = hasInv r ==>
                                    testSoundnessBin main side (runB boxXRule)
    where main        = (at i $ box r a, c)
          side        = (at j $ diam inv_r (nom i), d)
          Just inv_r  = invRel r

prop_subsIsSound_boxX :: NomSym
                      -> RelSym
                      -> (Formula Opaque, BasicClause)
                      -> (Formula Nom, BasicClause)
                      -> Property
prop_subsIsSound_boxX i r (a,c) (j,d) = hasInv r ==>
                                        testSubsBin main side (runB boxXRule)
    where main       = (at i $ box r a, c)
          side       = (at i $ diam inv_r j, d)
          Just inv_r = invRel r

prop_emptyness_boxX :: NomSym
                    -> RelSym
                    -> (Formula Opaque, BasicClause)
                    -> (Formula Nom, BasicClause)
                    -> Property
prop_emptyness_boxX i r (a,c) (j,d) = hasInv r ==>
                                      testEmptynessBin main side (runB boxXRule)
    where main       = (at i $ box r a, c)
          side       = (at i $ diam inv_r j, d)
          Just inv_r = invRel r

prop_emptyness_dia :: Formula (At (Diam Opaque)) -> BasicClause -> Bool
prop_emptyness_dia f c = testEmptynessUna (f,c) (runU diaRule)


prop_isSound_down :: Formula (At (Down Opaque)) -> BasicClause -> Property
prop_isSound_down f c = testSoundnessUna (f,c) (runU downRule)

prop_emptyness_down :: Formula (At (Down Opaque)) -> BasicClause -> Bool
prop_emptyness_down f c = testEmptynessUna (f,c) (runU downRule)


prop_isSound_conj :: Formula (At Conj) -> BasicClause -> Property
prop_isSound_conj f c = testSoundnessUna (f,c) (runU conjRule)

prop_emptyness_conj :: Formula (At Conj) -> BasicClause -> Bool
prop_emptyness_conj f c = testEmptynessUna (f,c) (runU conjRule)


prop_isSound_disj :: Formula (At Disj) -> BasicClause -> Property
prop_isSound_disj f c = testSoundnessUna (f,c) (runU disjRule)

prop_emptyness_disj :: Formula (At Disj) -> BasicClause -> Bool
prop_emptyness_disj f c = testEmptynessUna (f,c) (runU disjRule)


prop_isSound_parP :: NomSym
                  -> (Formula Prop, BasicClause)
                  -> (Formula Nom,[Formula (At Nom)])
                  -> Property
prop_isSound_parP i (p,c) (j,d) = testSoundnessBin main side (runB parPropRule)
    where main = (at i p, c)
          side = (at i j, fromList d)

prop_subsIsSound_parP :: NomSym
                      -> (Formula Prop, BasicClause)
                      -> (Formula Nom,[Formula (At Nom)])
                      -> Property
prop_subsIsSound_parP i (p,c) (j,d) = testSubsBin main side (runB parPropRule)
    where main = (at i p, c)
          side = (at i j, fromList d)

prop_emptyness_parP :: NomSym
                    -> (Formula Prop, BasicClause)
                    -> (Formula Nom,[Formula (At Nom)])
                    -> Bool
prop_emptyness_parP i (p,c) (j,d) = testEmptynessBin m s (runB parPropRule)
    where m = (at i p, c)
          s = (at i j, fromList d)


prop_isSound_parNP :: NomSym
                   -> (Formula Prop, BasicClause)
                   -> (Formula Nom,[Formula (At Nom)])
                   -> Property
prop_isSound_parNP i (p,c) (j,d) = testSoundnessBin m s (runB parNegPropRule)
    where m = (at i $ neg p, c)
          s = (at i j, fromList d)

prop_subsIsSound_parNP :: NomSym
                       -> (Formula Prop, BasicClause)
                       -> (Formula Nom,[Formula (At Nom)])
                       -> Property
prop_subsIsSound_parNP i (p,c) (j,d) = testSubsBin m s (runB parNegPropRule)
    where m = (at i $ neg p, c)
          s = (at i j, fromList d)

prop_emptyness_parNP :: NomSym
                     -> (Formula Prop, BasicClause)
                     -> (Formula Nom,[Formula (At Nom)])
                     -> Bool
prop_emptyness_parNP i (p,c) (j,d) = testEmptynessBin m s (runB parNegPropRule)
    where m = (at i $ neg p, c)
          s = (at i j, fromList d)


prop_isSound_parB :: NomSym
                  -> (Formula (Box Opaque), BasicClause)
                  -> (Formula Nom,[Formula (At Nom)])
                  -> Property
prop_isSound_parB i (f,c) (j,d) = testSoundnessBin main side (runB parBoxRule)
    where main = (at i f, c)
          side = (at i j, fromList d)

prop_subsIsSound_parB :: NomSym
                      -> (Formula (Box Opaque), BasicClause)
                      -> (Formula Nom,[Formula (At Nom)])
                      -> Property
prop_subsIsSound_parB i (f,c) (j,d) = testSubsBin main side (runB parBoxRule)
    where main = (at i f, c)
          side = (at i j, fromList d)

prop_emptyness_parB :: NomSym
                    -> (Formula (Box Opaque), BasicClause)
                    -> (Formula Nom,[Formula (At Nom)])
                    -> Bool
prop_emptyness_parB i (f,c) (j,d) = testEmptynessBin main side (runB parBoxRule)
    where main = (at i f, c)
          side = (at i j, fromList d)


prop_emptyness_parR :: NomSym
                     -> (Formula (Diam Nom), BasicClause)
                     -> (Formula Nom,[Formula (At Nom)])
                     -> Bool
prop_emptyness_parR i (f,c) (j,d) = testEmptynessBin m s (runB parRelRule)
    where m = (at i f, c)
          s = (at i j, fromList d)


prop_isSound_parEq :: NomSym
                   -> (Formula Nom, BasicClause)
                   -> (Formula Nom, [Formula (At Nom)])
                   -> Property
prop_isSound_parEq i (j,c) (k,d) = testSoundnessBin main side (runB parEqRule)
    where main = (at i j, c)
          side = (at i k, fromList d)

prop_subsIsSound_parEq :: NomSym
                       -> (Formula Nom, BasicClause)
                       -> (Formula Nom, [Formula (At Nom)])
                       -> Property
prop_subsIsSound_parEq i (j,c) (k,d) = testSubsBin main side (runB parEqRule)
    where main = (at i j, c)
          side = (at i k, fromList d)

prop_emptyness_parEq :: NomSym
                     -> (Formula Nom, BasicClause)
                     -> (Formula Nom, [Formula (At Nom)])
                     -> Bool
prop_emptyness_parEq i (j,c) (k,d) = testEmptynessBin main side (runB parEqRule)
    where main = (at i j, c)
          side = (at i k, fromList d)


prop_isSound_parNeq :: NomSym
                    -> (Formula (Neg Nom), BasicClause)
                    -> (Formula Nom, [Formula (At Nom)])
                    -> Property
prop_isSound_parNeq i (j,c) (k,d) = testSoundnessBin main side (runB parNeqRule)
    where main = (at i j, c)
          side = (at i k, fromList d)

prop_subsIsSound_parNeq :: NomSym
                       -> (Formula (Neg Nom), BasicClause)
                       -> (Formula Nom, [Formula (At Nom)])
                       -> Property
prop_subsIsSound_parNeq i (j,c) (k,d) = testSubsBin main side (runB parNeqRule)
    where main = (at i j, c)
          side = (at i k, fromList d)

prop_emptyness_parNeq :: NomSym
                      -> (Formula (Neg Nom), BasicClause)
                      -> (Formula Nom, [Formula (At Nom)])
                      -> Bool
prop_emptyness_parNeq i (j,c) (k,d) = testEmptynessBin m s (runB parNeqRule)
    where m = (at i j, c)
          s = (at i k, fromList d)

testSoundnessUna :: MainPremiseF (At f)
                 -> (MainPremiseF (At f) -> UnaRuleResult)
                 -> Property
testSoundnessUna mp rule =
      forAll (modelFor sig) $ \m ->
        m |= main ==> and [m |= e | e <- cons]
  where main   = uncurry add mp
        sig    = getSignature $ foldr1 union (main:cons)
        cons   = consequentsU result
        result = rule mp


testSoundnessBin :: MainPremiseF (At f)
                 -> SidePremiseF (At g)
                 -> (MainPremiseF (At f)
                  -> SidePremiseF (At g)
                  -> BinRuleResult)
                 -> Property
testSoundnessBin mp sp rule =
      forAll (modelFor sig) $ \m ->
         m |= side && m |= main ==> and [m |= e | e <- cons]
  where
        main   = uncurry add mp
        side   = uncurry add sp
        sig    = getSignature $ foldr1 union (main:side:cons)
        cons   = consequentsB result
        result = rule mp sp


testSubsBin :: MainPremiseF (At f)
            -> SidePremiseF (At g)
            -> (MainPremiseF (At f)
             -> SidePremiseF (At g)
             -> BinRuleResult)
            -> Property
testSubsBin (f,c) (f',d) rule =
    (not $ isTrivTaut main) && (not $ isTrivTaut side) &&
    (subs_main /= None || subs_side /= None) ==>
    --
    case (subs_main, subs_side) of
      (None, _) -> side_ok
      (_, None) -> main_ok
      _         -> forAll arbitrary $ \b -> pickPremise b
    --
  where mp        = (f, delete f c)
        sp        = (f', delete f' d)
        main      = uncurry add mp
        side      = uncurry add sp
        sig       = getSignature $ foldr1 union (main:side:cons)
        cons      = consequentsB result
        result    = rule mp sp
        subs_main = mainPremiseSubsumption result
        subs_side = sidePremiseSubsumption result
        --
        pickPremise True  = main_ok
        pickPremise False = side_ok
        --
        main_ok = case subs_main of
                    None      -> QC.label "none(main)" $
                                   not (any (`subset` main) cons)
                    IsSubset  -> QC.label "subset(main)" $
                                   any (`subset` main) cons
                    Semantic  -> QC.label "semantic(main)" $
                                   forAll (modelFor sig) $ \m ->
                                     m |= side && and [m |= e | e <- cons] ==>
                                        m |= main
                    ByParUnit -> QC.label "parunit(main)" False
        --
        side_ok = case subs_side of
                    None      -> QC.label "none(side)" $
                                   not $ any (`subset` side) cons
                    IsSubset  -> QC.label "subset(side)" $
                                   any (`subset` side) cons
                    Semantic  -> QC.label "semantic(side)" $
                                   forAll (modelFor sig) $ \m ->
                                     m |= main && and [m |= e | e <- cons] ==>
                                        m |= side
                    ByParUnit -> QC.label "parunit(side)" False

testEmptynessUna :: MainPremiseF (At f)
                 -> (MainPremiseF (At f) -> UnaRuleResult)
                 -> Bool
testEmptynessUna mp rule = any isEmpty cons == emptyClauseWasDerivedU result
    where cons   = consequentsU result
          result = rule mp


testEmptynessBin :: MainPremiseF (At f)
                 -> SidePremiseF (At g)
                 -> (MainPremiseF (At f)
                  -> SidePremiseF (At g)
                  -> BinRuleResult)
                 -> Bool
testEmptynessBin mp sp rule = any isEmpty cons == emptyClauseWasDerivedB result
    where cons   = consequentsB result
          result = rule mp sp


unit_tests :: UnitTest
unit_tests = [
    ("resP rule is sound",               runTest prop_isSound_resP),
    ("resP rule subsumption is sound",   runTest prop_subsIsSound_resP),
    ("resP rule emptyness test",         runTest prop_emptyness_resP),
    --
    ("resB rule is sound",               runTest prop_isSound_resB),
    ("resB rule subsumption is sound",   runTest prop_subsIsSound_resB),
    ("resB rule emptyness test",         runTest prop_emptyness_resB),
    --
    ("box rule is sound",                runTest prop_isSound_box),
    ("box rule subsumption is sound",    runHardestTest prop_subsIsSound_box),
    ("box rule emptyness test",          runTest prop_emptyness_box),
    --
    ("boxX rule is sound",               runTest prop_isSound_boxX),
    ("boxX rule subsumption is sound",   runHardestTest prop_subsIsSound_boxX),
    ("boxX rule emptyness test ",        runTest prop_emptyness_boxX),
    --
    -- diam is not sound, but satisfiability preserving. how can we test it?
    --
    ("diam rule emptyness test",         runTest prop_emptyness_dia),
    --
    ("down rule is sound",               runTest prop_isSound_down),
    ("down rule emptyness test",         runTest prop_emptyness_down),
    --
    ("conj rule is sound",               runTest prop_isSound_conj),
    ("conj rule emptyness test",         runTest prop_emptyness_conj),
    --
    ("disj rule is sound",               runTest prop_isSound_disj),
    ("disj rule emptyness test",         runTest prop_emptyness_disj),
    --
    ("parP rule is sound",               runTest prop_isSound_parP),
    ("parP rule subsumption is sound",   runHarderTest prop_subsIsSound_parP),
    ("parP rule emptyness test",         runTest prop_emptyness_parP),
    --
    ("parNP rule is sound",              runTest prop_isSound_parNP),
    ("parNP rule subsumption is sound",  runHarderTest prop_subsIsSound_parNP),
    ("parNP rule emptyness test",        runTest prop_emptyness_parNP),
    --
    ("parB rule is sound",               runTest prop_isSound_parB),
    ("parB rule subsumption is sound",   runHarderTest prop_subsIsSound_parB),
    ("parB rule emptyness test",         runTest prop_emptyness_parB),
    --
    -- parRel is not sound, but satisfiability preserving (at least
    -- if the target rel nom is not an inputNom). how can we test it?
    --
    ("parR rule emptyness test",         runTest prop_emptyness_parR),
    --
    ("parEq rule is sound",              runTest prop_isSound_parEq),
    ("parEq rule subsumption is sound",  runHarderTest prop_subsIsSound_parEq),
    ("parEq rule emptyness test",        runTest prop_emptyness_parEq),
    --
    ("parNeq rule is sound",             runTest prop_isSound_parNeq),
    ("parNeq rule subsumption is sound", runHarderTest prop_subsIsSound_parNeq),
    ("parNeq rule emptyness test",       runTest prop_emptyness_parNeq)
  ]

runHardestTest :: Testable a => a -> TestCase
runHardestTest = runTestWith defaultConfig{configMaxFail = 500000,
                                        configMaxTest = 50,
                                        configSize = f}
    where f = (1 +) . round . (log :: Float -> Float) . fromIntegral

runHarderTest :: Testable a => a -> TestCase
runHarderTest = runTestWith defaultConfig{configMaxFail = 10000}

