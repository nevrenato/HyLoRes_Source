module HyLoRes.Config ( Params(..) )

where

import HyLoRes.Logger ( LoggerCfg )

data Params = P {
               loggerCfg  :: LoggerCfg, -- what to log
               clausesOrd :: String,    -- Ordering criteria for Clauses
               timeoutVal :: Int,       -- Timeout in seconds
               bwSubsIsOn :: Bool,
               actModal   :: Bool,      -- Modal Formulas in Input?
               actHybr    :: Bool       -- Hybrid Formulas in Input?
              }
