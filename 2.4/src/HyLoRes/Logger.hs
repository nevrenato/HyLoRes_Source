module HyLoRes.Logger (
    MonadLogger(..), LoggerT, runLoggerT, LoggerCfg(..),

    LoggerEvent(..), log
 )

where

import Prelude hiding ( log )

import Control.Monad.Trans  ( MonadTrans(lift), MonadIO(liftIO) )
import Control.Monad.Reader ( ReaderT, asks, runReaderT )

import Data.List ( intersperse )

data LoggerCfg = LoggerCfg{logState :: Bool,
                           logRules :: Bool,
                           logComm  :: Bool}

data LoggerData = D {cfg     :: LoggerCfg,
                     prefix  :: String}

newtype LoggerT m a = LoggerT (ReaderT LoggerData m a)
                      deriving (Functor, Monad, MonadTrans, MonadIO)

data LoggerEvent = L_State | L_Rules | L_Comm | L_Metric | L_Debug

class Monad m => MonadLogger m where
    mustLogEvent :: LoggerEvent -> m Bool
    performLog   :: String -> m ()

instance MonadIO m => MonadLogger (LoggerT m) where
    mustLogEvent L_State  = fromData (logState . cfg)
    mustLogEvent L_Rules  = fromData (logRules . cfg)
    mustLogEvent L_Metric = return True
    mustLogEvent L_Comm   = fromData (logComm  . cfg)
    mustLogEvent L_Debug  = return True
    --
    performLog s =
        do pref <- fromData prefix
           let addPrefix = (pref ++) . concat . intersperse ('\n':pref) . lines
           liftIO $ putStrLn (addPrefix s)

instance (MonadLogger m, MonadTrans t, Monad (t m)) => MonadLogger (t m) where
    mustLogEvent = lift . mustLogEvent
    performLog   = lift . performLog

fromData :: Monad m => (LoggerData -> a) -> LoggerT m a
fromData f = LoggerT (asks f)

log :: MonadLogger m => LoggerEvent -> String ->  m ()
log e msg = do mustLog <- mustLogEvent e
               case mustLog of
                 False -> return ()
                 True  -> performLog msg

runLoggerT :: MonadIO m => LoggerT m a -> (String, LoggerCfg) -> m a
runLoggerT (LoggerT m) (p,c) = m `runReaderT` D{cfg = c, prefix = p}