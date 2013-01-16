module HyLoRes.Util.Ordering (flipOrd,
                              --
                              metap_trichotomy,
                              metap_irreflexive,
                              metap_antisymmetric,
                              metap_transitive)

where

import Test.QuickCheck((==>), Property)

flipOrd :: Ordering -> Ordering
flipOrd EQ = EQ
flipOrd GT = LT
flipOrd LT = GT

-- ============================================= --
--             QuickCheck stuff                  --
-- ============================================= --

metap_trichotomy :: Eq t => (t -> t -> Ordering) -> t -> t -> Bool
metap_trichotomy ord s t = (s == t) || (s `ord` t /= EQ)

metap_irreflexive :: (t -> t -> Ordering) -> t -> Bool
metap_irreflexive ord s = s `ord` s == EQ

metap_antisymmetric :: (t -> t -> Ordering) -> t -> t -> Bool
metap_antisymmetric ord s t = (s `ord` t) == (flipOrd $ t `ord` s)

metap_transitive :: (t -> t -> Ordering) -> t -> t -> t -> Property
metap_transitive ord s t r = (s `ord` t == GT && t `ord` r == GT)
                               ==> s `ord` r == GT


