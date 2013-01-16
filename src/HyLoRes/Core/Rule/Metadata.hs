----------------------------------------------------
--                                                --
-- HyLoRes.Core.Rule.Metadata:                    --
-- Miscelaneous rule data/info, that probably     --
-- should go in Rules.Base but didn't work due to --
-- mutually recursive modules and the 'deriving'  --
-- clause....                                     --
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

module HyLoRes.Core.Rule.Metadata( RuleId(..), PremiseType(..), opposite,
                                   Subsumption(..) )

where

import Data.Ix

data RuleId = R_ResP     -- Resolution on propositions
            | R_ResN     -- Resolution on nominals
            | R_ResB     -- Resolution on boxes
            --
            | R_Box      -- ([r]) rule
            | R_BoxX     -- Crossed version of the ([r]) rule (past modality)
            --
            | R_Dia      -- (<r>) rule (using nom function)
            --
            | R_Down     -- Down arrow elimination
            --
            | R_Disj     -- Disjunction elimination
            | R_Conj     -- Conjunction elimination
            -- == --
            | R_ParUnit  -- Unit full clause paramodulation
            ---
            | R_ParP     -- Labelled paramodulation on positive propositions
            | R_ParNegP  -- Labelled paramodulation on negative propositions
            ---
            | R_ParB     -- Labelled paramodulation on boxes (but replacing all
                         -- nominals occurring in the formula)
            | R_ParEq    -- Labelled paramodulation on equalities
            | R_ParNeq   -- Labelled paramodulation on inequalities
            ---
            | R_ParR     -- Labelled paramodulation on the relations
        deriving (Eq, Ord, Ix, Bounded, Show)

data PremiseType = Main | Side deriving (Show)

opposite :: PremiseType -> PremiseType
opposite Main = Side
opposite Side = Main

-- Ways in which a premise may get subsumed:
data Subsumption = None      -- no subsumption at all,
                 | IsSubset  -- using the standard redundancy criteria
                 | ByParUnit -- ParUnit-rule was applied
                 | Semantic  -- the clause is redundant because of "semantic"
                             -- reasons (the other premise and/or the consequent
                             -- carry the same information)
                 deriving ( Eq, Show, Read )
