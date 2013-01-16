----------------------------------------------------
--                                                --
-- HyLoRes.Util:                                  --
-- General use functions                          --
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

module HyLoRes.Util

where

import Data.List(intersperse)
import Data.Map(Map, insertWith, insertLookupWithKey)

infixr $.
($.) :: (c -> c') -> (a -> b -> c) -> (a -> b -> c')
($.) = (.) . (.)

{- filterFirst:
   Removes the first (i.e. leftmost) occurrence that satisfies f
-}
filterFirst :: (a -> Bool) -> [a] -> [a]
filterFirst _  []    = []
filterFirst f (x:xs) = if f x then xs else (x:(filterFirst f xs))

{- partition: Given

  - a predicate p (a -> Bool)
  - l, a list of [a]

  returns a pair (l1, l2) such that l1 ++ l2 is a permutation of l
  and x appears in l1 iff p x is True
-}
partition :: (a -> Bool) -> [a] -> ([a], [a])
partition _  []    = ([], [])
partition p (x:xs) = if p x then (x:posxs, negxs) else (posxs, x:negxs)
                  where (posxs, negxs) = partition p xs

compareUsing :: Ord b => (a -> b) -> a -> a -> Ordering
compareUsing f x y = compare (f x) (f y)

{- both: Given

  - a predicate p1
  - a predicate p2

  returns True iff both p1(x) and p2(x) return True
-}
both :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
both p1 p2 x = (p1 x) && (p2 x)

{- atLeastOne: Given

  - a predicate p1
  - a predicate p2
  - an element x

  returns True iff p1(x) or p2(x) return True
-}
atLeastOne :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
atLeastOne p1 p2 x = (p1 x) || (p2 x)

insertLookup :: Ord k => k -> v -> Map k v -> (Maybe v, Map k v)
insertLookup = insertLookupWithKey (\_ _ oldVal -> oldVal)

adjustOrInsert ::  Ord k => (v -> v) -> k -> v -> Map k v -> Map k v
adjustOrInsert f = insertWith (const f)

{- separate: Given

  - a separator s
  - a list l of some instance of Show

  returns a String that "shows" all the elements of l,
  separating every contiguous elements with s
-}
separate :: Show a => String -> [a] -> String
separate s = concat . intersperse s . map show

{- commaSeparate: Given

  - a list l of some instance of Show

  returns a String with all the elements of l separated by commas
-}
commaSeparate :: Show a => [a] -> String
commaSeparate l = separate ", " l

{- commaSeparateHdr: Given

  - a string which represents a header
  - a list l of some instance of Show

  returns a String with the header, followed by all the elements
  of l separated by commas, one below the other, and properly indented.
-}
commaSeparateHdr :: Show a => String -> [a] -> String
commaSeparateHdr hdr l = hdr ++ (separate separator l)
           where separator = ",\n" ++ indent
                 indent    = map (const ' ') hdr

{- printcommaSeparateHdr: Given

  - a string which represents a header
  - a list l of some instance of Show

  prints the header, followed by all the elements
  of l separated by commas, one below the other, and properly indented.
-}
printCommaSeparateHdr :: Show a => String -> [a] -> IO ()
printCommaSeparateHdr hdr l = do
                             let indent    = map (const ' ') hdr
                             let separator = ",\n" ++ indent
                             putStr hdr;
                             putStr (separate separator l)

showListWith :: (a -> ShowS) -> ShowS -> [a] -> ShowS -> ShowS
showListWith f open xs close = open . commaSep xs . close
    where commaSep = foldr1 (.) . intersperse (showString ", ") . map f

data ShowRight = ShowRight String

instance Show ShowRight where
    show (ShowRight s) = s
