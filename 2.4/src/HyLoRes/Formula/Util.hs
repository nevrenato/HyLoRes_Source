module HyLoRes.Formula.Util ( isTrivTrue, isTrivFalse, isAtNegLit )

where

import HyLoRes.Formula.TypeLevel ( Spec(..) )

import HyLoRes.Formula ( Formula, At, flatten, specialize )

isTrivFalse :: Formula (At f) -> Bool
isTrivFalse f = case specialize f of
                    AtNegTop{}  -> True
                    AtNegNom f' -> (uncurry (==) . flatten) f'
                    _           -> False

isTrivTrue :: Formula (At f) -> Bool
isTrivTrue f = case specialize f of
                   AtTop{}  -> True
                   AtNom f' -> (uncurry (==) . flatten) f'
                   _        -> False

isAtNegLit :: Formula (At f) -> Bool
isAtNegLit f = case specialize f of
                   AtNegProp{} -> True
                   AtNegNom{}  -> True
                   _           -> False
