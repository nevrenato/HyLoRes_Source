module HyLoRes.ModelGen ( HerbrandModel, buildHerbrandModel,
                          inducedModel, expand )

where

import Control.Applicative ( (<$>) )

import Control.Monad.State ( State, get, put, evalState, execState,
                              when, liftM2 )

import Data.List ( sort )

import Data.Set ( Set )
import qualified Data.Set as Set

import Data.Map ( Map, (!) )
import qualified Data.Map as Map

import Data.Maybe    ( fromJust )

import HyLo.Model          ( (|/=) )
import HyLo.Model.Herbrand ( inducedModel, expand, removeWorld )
import qualified HyLo.Model          as M
import qualified HyLo.Model.Herbrand as H

import HyLoRes.ClauseSet.InUse ( InUseClauseSet, allClausesOpaquedIdx,
                                 unitEqIdx, nonUnitEqIdx,
                                 atPropIdx, atDiaNomIdx )

import HyLo.Signature ( buildSignature, nomSymbols )
import qualified HyLo.Signature.Simple as S

import HyLoRes.Clause             ( toFormulaList )
import HyLoRes.Clause.FullClause  ( FullClause, distFormula, splitAtDist,
                                    specialize )

import HyLoRes.Formula ( At, Opaque,
                         Signature, NomSym, RelSym(..), PropSym, NomId,
                         isInputNom, inputNom, nomId, isVar,
                         label, flatten, spyU )
import HyLoRes.Formula.NF ( fromNF )
import HyLoRes.Formula.TypeLevel ( Spec(..) )

import HyLoRes.Formula.Transformations ( fromHyLoResNom, fromHyLoResProp,
                                         fromHyLoResRel )


type HerbrandModel = H.HerbrandModel S.NomSymbol S.PropSymbol S.RelSymbol

buildHerbrandModel :: Signature -> InUseClauseSet -> HerbrandModel
buildHerbrandModel input_sig iu = evalState go (nextNomId, Map.empty)
  where nextNomId    = 1 + maxNomId all_noms
        all_noms     = filter (not . isVar) . Set.toList $ nomSymbols input_sig
        --
        (_,es,ps,rs) = execState (mapM_ eps cls) (m_ids,ids,Set.empty,Set.empty)
        cls          = sort $ concat [allClausesOpaquedIdx (unitEqIdx    iu),
                                      allClausesOpaquedIdx (nonUnitEqIdx iu),
                                      allClausesOpaquedIdx (atPropIdx    iu),
                                      allClausesOpaquedIdx (atDiaNomIdx  iu)]
        ids          = Set.fromList [(i,i) | i <- all_noms]
        m_ids        = Map.fromList [(i,i) | i <- all_noms]
        --
        (rsU,rsNU)  = Set.partition hasUnivMod rs
        mkNomsU     = concatMap (\(i,_,j) -> [i,j]) . Set.toList
        --
        hasUnivMod (_,r,_) = r == Univ
        f g s  = Set.fromList <$> mapM g (Set.toList s)
        go           = do es'   <- f (fmap toSimpleSigE . useInputNomsE) es
                          ps'   <- f (fmap toSimpleSigP . useInputNomsP) ps
                          rs'   <- f (fmap toSimpleSigR . useInputNomsR) rsNU
                          --
                          let i_n = (H.herbrand es' ps' rs')
                          --
                          spyU' <- fromHyLoResNom <$> mapNomInserting spyU
                          nomsU <- Set.delete spyU'    .
                                   Set.fromList        .
                                   map fromHyLoResNom <$>
                                   (mapM mapNomInserting $ mkNomsU rsU)
                          let s' = buildSignature nomsU Set.empty Set.empty
                          --
                          return $ expand s' (removeWorld spyU' i_n)


eps :: FullClause (At Opaque)
    -> State (Map NomSym NomSym,
              Set (NomSym, NomSym),
              Set (NomSym, PropSym),
              Set (NomSym, RelSym, NomSym)) ()
eps c =
    do (m_es, es,ps,rs) <- get
       --
       let i_c    = inducedModel $ H.herbrand es ps rs
       --
       let weak_reduced f = let i = label $ f
                            in  i == M.valN i_c i
           tr_false f     = case specialize f of
                                AtNom f'    -> or [ i_c |/= f,
                                                    let (i, j) = flatten f'
                                                    in m_es ! i > j]
                                AtDiamNom{} -> i_c |/= f
                                _           -> i_c |/= f
                            -- in this context, i think it suffices
                            -- to test for false, and by
                            -- construction it will imply tr-false
       --
       when ( weak_reduced (distFormula c) && all tr_false (rest c) ) $
         case specialize c of
           AtNom cl     -> put (uncurry Map.insert (flatten $ distF cl) m_es,
                                Set.insert (flatten $ distF cl) es,
                                ps,
                                rs)
           AtProp cl    -> when ( i_c |/= distF cl ) $
                             put (m_es,es,Set.insert (flatten $ distF cl) ps,rs)
           AtDiamNom cl -> when ( i_c |/= distF cl ) $
                             put (m_es,es,ps,Set.insert (flatten $ distF cl) rs)
           _            -> err
    where err     = error "buildHerbrandModel: unexpected distFormula type"
          distF   = distFormula
          rest    = map fromNF . toFormulaList . snd . splitAtDist


maxNomId :: [NomSym] -> NomId
maxNomId ns = fromJust . maximum $ Just 0 : [nomId i | i <- ns]

type NomCleaner = State (NomId, Map NomSym NomSym)

useInputNomsE :: (NomSym, NomSym) -> NomCleaner (NomSym, NomSym)
useInputNomsE (i,j) = liftM2 (,) (mapNomInserting i) (mapNomInserting j)

useInputNomsP :: (NomSym, PropSym) -> NomCleaner (NomSym, PropSym)
useInputNomsP (i,p) = do i' <- mapNomInserting i; return (i',p)

useInputNomsR :: (NomSym, RelSym, NomSym) -> NomCleaner (NomSym, RelSym, NomSym)
useInputNomsR (i,r,j) = do i' <- mapNomInserting i
                           j' <- mapNomInserting j
                           return (i', r, j')

mapNomInserting :: NomSym -> NomCleaner NomSym
mapNomInserting i
    | isInputNom i = return i
    | otherwise    = do (next, m) <- get
                        case Map.lookup i m of
                          Nothing -> do let j = inputNom next
                                        put (next+1, Map.insert i j m)
                                        return j
                          Just j  -> return j

toSimpleSigE :: (NomSym, NomSym) -> (S.NomSymbol, S.NomSymbol)
toSimpleSigE (i,j) = (fromHyLoResNom i, fromHyLoResNom j)

toSimpleSigP :: (NomSym, PropSym) -> (S.NomSymbol, S.PropSymbol)
toSimpleSigP (i,p) = (fromHyLoResNom i, fromHyLoResProp p)

toSimpleSigR :: (NomSym,RelSym,NomSym) -> (S.NomSymbol,S.RelSymbol,S.NomSymbol)
toSimpleSigR (i,r,j) = (fromHyLoResNom i, fromHyLoResRel r, fromHyLoResNom j)
