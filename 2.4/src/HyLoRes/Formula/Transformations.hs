module HyLoRes.Formula.Transformations ( fromSimpleSig, toSimpleSig,
                                         --
                                         fromHyLoResNom,  toHyLoResNom,
                                         fromHyLoResProp, toHyLoResProp,
                                         fromHyLoResRel,  toHyLoResRel,
                                         --
                                         embedUnivMod,
                                         --
                                         unit_tests)
where

import Control.Applicative ( (<$>) )
import Control.Monad.State ( runState, get, put, liftM2, when )

import Data.Maybe ( catMaybes )
import qualified Data.Set as Set

import qualified HyLo.Formula          as F
import qualified HyLo.Signature.Simple as S

import HyLo.Test ( UnitTest, runTest )

import HyLoRes.Formula ( NomSym, PropSym(..), RelSym(..),
                         inputNom, nomId, isInputNom,
                         var, varId,
                         evalPoint, spyU )


fromSimpleSig :: F.Formula S.NomSymbol S.PropSymbol S.RelSymbol
              -> F.Formula NomSym PropSym RelSym
fromSimpleSig = F.mapSig toHyLoResNom toHyLoResProp toHyLoResRel

toSimpleSig :: F.Formula NomSym PropSym RelSym
            -> F.Formula S.NomSymbol S.PropSymbol S.RelSymbol
toSimpleSig = F.mapSig fromHyLoResNom
                       fromHyLoResProp
                       fromHyLoResRel

toHyLoResNom :: S.NomSymbol -> NomSym
toHyLoResNom  (S.N i) = inputNom (fromIntegral i)
toHyLoResNom  (S.X x) = var (fromIntegral x)

fromHyLoResNom :: NomSym -> S.NomSymbol
fromHyLoResNom i
    | isInputNom i = maybe (error "fromHyLoResNom: input nom expected")
                           (S.N . fromIntegral)
                           (nomId i)
    | otherwise    = maybe (error "fromHyLoResNom: var expected")
                           (S.X . fromIntegral)
                           (varId i)


toHyLoResProp :: S.PropSymbol -> PropSym
toHyLoResProp (S.PropSymbol p) = P p

fromHyLoResProp :: PropSym -> S.PropSymbol
fromHyLoResProp (P p) = S.PropSymbol p

toHyLoResRel :: S.RelSymbol -> RelSym
toHyLoResRel  (   S.RelSymbol r) = Rel r
toHyLoResRel  (S.InvRelSymbol r) = RelInv r

fromHyLoResRel :: RelSym -> S.RelSymbol
fromHyLoResRel  (Rel    r) = S.RelSymbol    r
fromHyLoResRel  (RelInv r) = S.InvRelSymbol r
fromHyLoResRel   Univ      = error "fromHyLoResRel: universal mod"

embedUnivMod :: [F.Formula NomSym PropSym RelSym]
             -> [F.Formula NomSym PropSym RelSym]
embedUnivMod fs = case runState (mapM embed fs) (Set.empty,Set.empty,False) of
                    (  _, ( _, _, False)) -> fs
                    (fs', (ns,rs, True))  -> concat [fs',
                                                     mkAxiomsN $ Set.toList ns,
                                                     mkAxiomsR $ Set.toList rs]
   where embed  F.Top         = return F.Top
         embed  F.Bot         = return F.Bot
         embed (F.Prop p)     = return (F.Prop p)
         embed (F.Nom  n)     = do when (isInputNom n) $
                                     addNom n
                                   return (F.Nom  n)
         --
         embed (F.Neg  f)     = F.Neg <$> embed f
         --
         embed (f F.:&: g)    = liftM2  (F.:&:)   (embed f) (embed g)
         embed (f F.:|: g)    = liftM2  (F.:|:)   (embed f) (embed g)
         embed (f F.:-->: g)  = liftM2 (F.:-->:)  (embed f) (embed g)
         embed (f F.:<-->: g) = liftM2 (F.:<-->:) (embed f) (embed g)
         --
         embed (F.Diam r f)   = do addRel r; F.Diam r <$> embed f
         embed (F.Box  r f)   = do addRel r; F.Box  r <$> embed f
         --
         embed (F.At  n f)    = do when (isInputNom n) $
                                     addNom n
                                   F.At  n <$> embed f
         --
         embed (F.A f)        = do univHit; F.At spyU . F.Box  Univ <$> embed f
         embed (F.E f)        = do univHit; F.At spyU . F.Diam Univ <$> embed f
         --
         embed (F.D f)        = embed (F.Down x . F.E $ F.Neg svar_x F.:&: f)
                                  where (x, svar_x) = (freshVar f, F.Nom x)
         embed (F.B f)        = embed (F.Down x . F.A $ F.Neg svar_x F.:-->: f)
                                  where (x, svar_x) = (freshVar f, F.Nom x)
         --
         embed (F.Down x f)   = F.Down x <$> embed f
         --
         addNom n = do (ns, rs, b) <- get; put (Set.insert n ns, rs, b)
         addRel r = do (ns, rs, b) <- get; put (ns, Set.insert r rs, b)
         univHit  = do (ns, rs, _) <- get; put (ns, rs, True)
         --
         mkAxiomsN ns = [F.At spyU . F.Diam Univ $ F.Nom n | n <- evalPoint:ns]
         mkAxiomsR rs = [F.At spyU . F.Box Univ . F.Box r $ reachable | r <- rs]
             where reachable = F.Down x . F.At spyU . F.Diam Univ $ F.Nom x
                       where x = var 1

freshVar :: F.Formula NomSym PropSym RelSym -> NomSym
freshVar = var . succ . maximum . (1 :) . catMaybes . map varId . F.freeVars

-- -----------------------------
-- QuickCheck stuff
-- -----------------------------

prop_simpleSig :: F.Formula S.NomSymbol S.PropSymbol S.RelSymbol -> Bool
prop_simpleSig f = f == (toSimpleSig . fromSimpleSig $ f)

unit_tests :: UnitTest
unit_tests = [("toSimpleSig/fromSimpleSig inverses", runTest prop_simpleSig)]

