module HyLoRes.Util.Timeout    ( withNoTimeout, notifyOnTimeout,
                                 TimeoutSignal,
                                 isTimeout, isNotTimeout ) where

import Control.Monad           ( liftM )
import Control.Monad.Trans     ( MonadIO, liftIO )
import Control.Concurrent      ( forkIO, threadDelay )
import Control.Concurrent.MVar ( MVar, newEmptyMVar, putMVar, isEmptyMVar )


newtype TimeoutSignal = TS {unTS :: MVar ()}


newTimeoutSignal :: IO TimeoutSignal
newTimeoutSignal = TS `liftM` newEmptyMVar

isTimeout :: MonadIO m => TimeoutSignal -> m Bool
isTimeout = liftM not . isNotTimeout

isNotTimeout :: MonadIO m => TimeoutSignal -> m Bool
isNotTimeout = liftIO . isEmptyMVar . unTS

signalTimeout :: TimeoutSignal -> IO ()
signalTimeout = flip putMVar () . unTS


notifyOnTimeout :: Int -> (TimeoutSignal -> IO a) -> IO a
notifyOnTimeout secs action = do timeout_signal <- newTimeoutSignal
                                 forkIO $ watchdog_thread timeout_signal
                                 action timeout_signal
    --
    where watchdog_thread ts = do threadDelay (secs * 1000000)
                                  signalTimeout ts

withNoTimeout :: (TimeoutSignal -> IO a) -> IO a
withNoTimeout = (newTimeoutSignal >>=)