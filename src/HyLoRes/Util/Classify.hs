----------------------------------------------------
--                                                --
-- HyLoRes.Util.Classify:                         --
-- Structures and functios for the                --
-- classification of  data                        --
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

module HyLoRes.Util.Classify(Classification, classifyBy,
                             classifyListBy, classifySetBy,
                             classifyListByM,
                             criteria2, criteria3)

where

import Data.List(foldl')
import Data.Foldable(foldlM)

import Data.Map(Map)
import qualified Data.Map as Map(empty, insertWith)

import Data.Set(Set)
import qualified Data.Set as Set(toList)

type Classification k v = Map k [v]

classifyBy :: Ord k => (v -> k) -> v -> Classification k v -> Classification k v
classifyBy criteria x = Map.insertWith (const (x:)) (criteria x) [x]

classifyListByM :: (Monad m, Ord k) => (v -> m k) -> [v] -> m (Classification k v)
classifyListByM criteria = foldlM (flip $ classifyByM criteria) Map.empty

classifyByM :: (Monad a, Ord k) => (v -> a k) -> v -> Classification k v -> a (Classification k v)
classifyByM criteria x m = do key <- criteria x
                              return $ Map.insertWith (const (x:)) key [x] m

classifyListBy :: Ord k => (v -> k) -> [v] -> Classification k v
classifyListBy criteria = foldl' (flip $ classifyBy criteria) Map.empty

classifySetBy :: Ord k => (v -> k) -> Set v -> Classification k v
classifySetBy criteria = classifyListBy criteria . Set.toList

criteria2 :: (a -> b) -> (a -> c) -> a -> (b, c)
criteria2 f1 f2 x = (f1 x, f2 x)

criteria3 :: (a -> b) -> (a -> c) -> (a -> d) -> a -> (b, c, d)
criteria3 f1 f2 f3 x = (f1 x, f2 x, f3 x)
