module Main ( main )

where

import Control.Monad ( when )
import System.Exit   ( exitFailure )

import HyLo.Test ( TestResult(OK), UnitTest, ModuleName,
                   stopOnError, testSuite )

import qualified HyLoRes.Formula                     ( unit_tests )
import qualified HyLoRes.Formula.NF                  ( unit_tests )
import qualified HyLoRes.Formula.Transformations     ( unit_tests )
import qualified HyLoRes.Clause.BasicClause          ( unit_tests )
import qualified HyLoRes.Clause.FullClause           ( unit_tests )
import qualified HyLoRes.ClauseSet.Clauses           ( unit_tests )
import qualified HyLoRes.ClauseSet.InUse             ( unit_tests )
import qualified HyLoRes.Subsumption.SubsumptionTrie ( unit_tests )
import qualified HyLoRes.Core.Rule.Definitions       ( unit_tests )

all_tests :: [(ModuleName, UnitTest)]
all_tests = [
    ("HyLoRes.Formula",               HyLoRes.Formula.unit_tests),
    ("HyLoRes.Formula.NF",            HyLoRes.Formula.NF.unit_tests),
    ("HyLoRes.Formula.Transformations",
                      HyLoRes.Formula.Transformations.unit_tests),
    ("HyLoRes.Clause.BasicClause",    HyLoRes.Clause.BasicClause.unit_tests),
    ("HyLoRes.Clause.FullClause",     HyLoRes.Clause.FullClause.unit_tests),
    ("HyLoRes.ClauseSet.Clauses",     HyLoRes.ClauseSet.Clauses.unit_tests),
    ("HyLoRes.ClauseSet.InUse",       HyLoRes.ClauseSet.InUse.unit_tests),
    ("HyLoRes.Subsumption.SubsumptionTrie",
                                HyLoRes.Subsumption.SubsumptionTrie.unit_tests),
    ("HyLoRes.Core.Rule.Definitions", HyLoRes.Core.Rule.Definitions.unit_tests)
  ]

main :: IO ()
main = do rs <- stopOnError testSuite all_tests
          when (not $ all (== OK) rs) $ do
               putStrLn "Some tests did not pass!"
               exitFailure
