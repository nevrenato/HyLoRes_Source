module HyLoRes.Core.SMP.Dispatcher(
    DispatcherChans(..), runDispatcher,
    DispatchAlgorithm (..), fromDispatchAlgString
)

where

import Prelude hiding ( log )

import Control.Monad.State
import Control.Monad.Reader

import Control.Concurrent.Chan

import Control.Applicative ( (<$>) )

import Data.Map ( Map )
import qualified Data.Map as Map

import Data.Set ( Set )
import qualified Data.Set as Set

import Data.Array    ( Array, (!), bounds, rangeSize )
import Data.List     (foldl', partition, sortBy)
import Data.Foldable ( foldMap )
import Data.Maybe    ( Maybe (..), catMaybes )

import HyLoRes.Util ( compareUsing )
import HyLo.Signature ( getSignature )

import HyLoRes.Clause ( size )
import HyLoRes.Clause.BasicClause ( BasicClause, mergeAllDiamonds)
import HyLoRes.Clause.FullClause  ( FullClause, ClauseId,
                                    distFormula, makeFullClause,
                                    specialize,
                                    opaqueClause )
import HyLoRes.Formula.TypeLevel ( Spec(..) )
import HyLoRes.Clause.SelFunction ( SelFunc )
import HyLoRes.ClauseSet.InUse    ( InUseClauseSet, add, newSet )
import qualified HyLoRes.ClauseSet.InUse as IU


import HyLoRes.Util.Timeout ( TimeoutSignal, isTimeout )

import HyLoRes.Formula ( NomSym, At, Nom, Opaque, label,
			 flatten, Diam, level, nomId)

import HyLoRes.Util.Classify ( classifyListByM )

import HyLoRes.Core.Worker.Base ( Result (..) )

import HyLoRes.Core.SMP.Base ( WorkerId,
                               ChDispatcherToMain,
                               ChWorkerToDispatcher,   ChDispatcherToWorker,
                               MsgDispatcherToWorker(..),
                               MsgWorkerToDispatcher(..) )

import HyLoRes.Logger ( MonadLogger, LoggerT, runLoggerT, LoggerCfg,
                        log, LoggerEvent(..) )

import HyLoRes.ModelGen ( buildHerbrandModel )

type DispatchFunc = NomSym -> Dispatcher (WorkerId)

type NomWorkerMap = Map NomSym WorkerId

type WorkerLoadMap = Map WorkerId Int

data DispatchAlgorithm = HASH | RROBIN | LOAD

data DispatcherChans = DC{dtoMain      :: ChDispatcherToMain,
                          toWorkers    :: Array WorkerId ChDispatcherToWorker,
                          fromWorkers  :: ChWorkerToDispatcher}

data DispatcherEnv = E{dispatcherChans :: DispatcherChans,
                       workerCount     :: Int,
                       timeout_signal  :: TimeoutSignal,
                       dispatchFunc    :: DispatchFunc}

newtype Dispatcher a = D{unD :: ReaderT DispatcherEnv   (
                                LoggerT                 (
                                StateT  DispatcherState (
                                IO))) a}
    deriving (Functor, Monad, MonadLogger, MonadIO)

instance MonadReader DispatcherEnv Dispatcher where
    ask   = D ask
    local r (D m) = D (local r m)


data DispatcherState =
    S{newClauses    :: [BasicClause],
      nextClId      :: ClauseId,
      workerMap     :: NomWorkerMap,
      workerLoadMap :: WorkerLoadMap,
      nextWorker    :: WorkerId,
      msgs          :: Map WorkerId (Set (FullClause (At Opaque)))}

instance MonadState DispatcherState Dispatcher where
    get   = D (lift . lift $ get)
    put s = D (lift . lift $ put s)


runDispatcher :: DispatcherChans
              -> LoggerCfg
              -> SelFunc
              -> [BasicClause]
              -> TimeoutSignal
              -> DispatchAlgorithm
              -> IO ()
runDispatcher chans lc sf init_cls ts da
    = (`evalStateT` initialState)
    . (`runLoggerT` ("[D]: ", lc))
    . (`runReaderT` env)
    . unD
    $ dispatcherLoop sf init_cls
    --
    where env = E{dispatcherChans = chans,
                  workerCount     = rangeSize . bounds $ toWorkers chans,
                  timeout_signal  = ts,
                  dispatchFunc    = selectAlg (workerCount env) da}
          --
          initialState = S{newClauses    = [],
                           nextClId      = 0,
                           workerMap     = Map.empty,
                           workerLoadMap = Map.empty,
                           msgs          = Map.empty,
                           nextWorker    = 0}

fromDispatchAlgString :: String -> DispatchAlgorithm
fromDispatchAlgString "HASH" = HASH
fromDispatchAlgString "RROBIN" = RROBIN
fromDispatchAlgString "LOAD" = LOAD
fromDispatchAlgString _ = undefined

selectAlg :: Int -> DispatchAlgorithm -> DispatchFunc
selectAlg n HASH = hash n
selectAlg n RROBIN = rrobin n
selectAlg n LOAD = load n

hash ::  Int -> NomSym -> Dispatcher (WorkerId)
hash n nom  = do let wId = maybe (fromIntegral $ level nom) fromIntegral (nomId nom)
                 return $ wId `mod` (fromIntegral n)

rrobin :: Int -> NomSym -> Dispatcher (WorkerId)
rrobin n nom = do s <- get
                  case Map.lookup nom (workerMap s) of
                    Just i  -> return i
                    Nothing -> do let nw = nextWorker s
                                  put s{nextWorker = (nw + 1) `mod` (fromIntegral n),
                                        workerMap = Map.insert nom nw (workerMap s) }
                                  return nw

load :: Int -> NomSym -> Dispatcher (WorkerId)
load _ nom = do s <- get
                case Map.lookup nom (workerMap s) of
                    Just i  -> return i
                    Nothing -> do let l = Map.toList (workerLoadMap s)
				  log L_Comm $ show l
                                  let nw = fst (foldl' f2 (0,10000000)  l)
                                  put s{workerMap = Map.insert nom nw (workerMap s)}
                                  return nw

f2 :: (WorkerId, Int) -> (WorkerId, Int) -> (WorkerId, Int)
f2 a b = if (snd a) < (snd b) then a else b

dispatcherLoop :: SelFunc -> [BasicClause] -> Dispatcher ()
dispatcherLoop sf init_cls =
    do addAllToNew init_cls
       n <- fromIntegral <$> (asks workerCount)
       forM_ [0..n-1] $ \workerId -> do
             modify $ \s -> s{workerLoadMap = Map.insert workerId 0 (workerLoadMap s)}
       wasSAT <- loopAux sf 0 0
       --
       sendStopToWorkers
       response <- if wasSAT
                      then do inuse <- getInUseFromWorkers
                              let init_sig = foldMap getSignature init_cls
                              return (SAT (buildHerbrandModel init_sig inuse ))
                      --
                      else return INTERRUPTED
       --
       mch <- channel dtoMain
       liftIO $ writeChan mch response

loopAux :: SelFunc -> Int -> Int -> Dispatcher Bool
loopAux sf counter waiting =
    do timeout <- isTimeout =<< asks timeout_signal
       if timeout
          then return False
          else do (dispatched, waiting') <- dispatchClauses waiting sf
                  log L_Comm $ concat [show dispatched, " more clauses dispatched"]
                  --
                  if (counter + dispatched > 0)
                     then do (processed, new) <- readWorkerMsgs
                             let num_received = length new
                             --
                             log L_Comm $ concat [show processed, " clauses processed by workers, ",
                                                  show num_received, " new clauses received"]
                             --
                             addAllToNew new
                             let currently_waiting = counter + dispatched - processed
                             log L_Comm $ concat ["Currently waiting for ", show currently_waiting,
                                                  " clauses, and ",
                                                  show $ length new, " to dispatch"]
                             --
                             if (currently_waiting > 0 || length new > 0)
                                then loopAux sf currently_waiting waiting'
                                else return True
                     else return True


dispatchClauses :: Int -> SelFunc -> Dispatcher (Int, Int)
dispatchClauses waiting sf =
    do new <- gets newClauses
       let sortedNew = sortBy (compareUsing size) new
       fullCls <- mapM (mkFullClause sf) sortedNew
       if ( length fullCls == 0)
	  then return (0, waiting)
          else do n <- asks workerCount
                  if (n == 1)
                     then do workers <- channel toWorkers
                             liftIO $ writeChan  (workers ! 0 ) (D2W_CLAUSES fullCls )
                             return $ ( length fullCls, waiting + (length fullCls))
                     else do df <- asks dispatchFunc
                             let (eq, notEq)  = partition isEq fullCls

                             cl <- classifyListByM (df . label . distFormula) notEq

                             when (not . null $ eq) $
                                  addToAllWorkers eq

                             let diam =  catMaybes $ map asRelDiam  notEq

                             cl2 <- classifyListByM (df . thrd . flatten .  distFormula) diam
                             mapM_ addToWorkerMsg (map (\(a,b) -> (a, b)) $ (Map.toList cl))
                             mapM_ addToWorkerMsg (map (\(a,b) -> (a, (map opaqueClause b))) $ (Map.toList cl2))
                             dispatched <- sendMsgsToWorkers
                             return $ (dispatched,waiting + dispatched)
    where thrd (_, _, x) = x

addToWorkerMsg ::  (WorkerId , [FullClause (At Opaque)]) -> Dispatcher ()
addToWorkerMsg (n,clauses)  =
    do s <- get
       let set = Map.findWithDefault Set.empty n (msgs s)
       let set' = Set.union set (Set.fromList clauses)
       put s {msgs = Map.insert n set' (msgs s)}

sendMsgsToWorkers :: Dispatcher (Int)
sendMsgsToWorkers = do n <- fromIntegral <$> (asks workerCount)
                       res <- forM [0..n-1] $ \workerId -> do
                                  s <- get
                                  workers <- channel toWorkers
                                  let set = Map.findWithDefault Set.empty workerId (msgs s)
                                  if (Set.size set) > 0
                                    then do let fcls = Set.toList set
                                            liftIO $ writeChan (workers ! workerId) (D2W_CLAUSES fcls)
 					    put s{workerLoadMap = Map.insertWith (+) workerId (length fcls) (workerLoadMap s)}
                                            log L_Comm $ concat ["Sent ", show (length $ (fcls)), " to Worker ", show workerId]
                                            return $ length fcls
                                    else return 0
                       modify $ \s -> s{msgs = Map.empty}
                       return $ sum res

isEq :: FullClause (At Opaque) -> Bool
isEq cl = case specialize cl of { AtNom c -> size c == 1; _ -> False }

asRelDiam :: FullClause (At Opaque) -> Maybe (FullClause (At (Diam Nom)))
asRelDiam cl = case specialize cl of { AtDiamNom c -> Just c; _ -> Nothing }


mkFullClause :: SelFunc -> BasicClause -> Dispatcher (FullClause (At Opaque))
mkFullClause sf cl = do s <- get
                        put s{nextClId = 1 + nextClId s}
                        return $ makeFullClause sf (nextClId s) cl

readWorkerMsgs :: Dispatcher (Int, [BasicClause])
readWorkerMsgs = do m <- asks workerCount
                    workerChan <- channel fromWorkers
                    res <- forM [0..m-1] $ \_ -> do
                              emptyChan <- liftIO $ isEmptyChan workerChan
                              if ( emptyChan )
                               then return (0,[])
                               else do NEW p n <- liftIO $ readChan workerChan
                                       return (p,n)
                    let r = foldl' f1 (0,[]) res
                    if (fst r == 0)
                       then do NEW p n <- liftIO $ readChan workerChan
                               return (p,n)
                       else return r

f1 :: (Int, [BasicClause]) -> (Int, [BasicClause]) -> (Int, [BasicClause])
f1 a b = ((fst a) + (fst b), (snd a) ++ (snd b))

addToNew :: BasicClause -> Dispatcher ()
addToNew cl = do s <- get
                 let cl' = mergeAllDiamonds cl
                 put s{newClauses = (newClauses s) ++ [cl']}


{- addAllToNew: Given

  - a list of BasicClauses
  - a ClauseSet cs

  adds all the given clauses to New (using addToNew)
-}
addAllToNew :: [BasicClause] -> Dispatcher ()
addAllToNew cls = do modify $ \s -> s{newClauses = []}
                     mapM_ addToNew cls


sendStopToWorkers :: Dispatcher ()
sendStopToWorkers =
    do n <- fromIntegral <$> (asks workerCount)
       forM_ [0..n-1] $ \workerId -> do
           workers <- channel toWorkers
           liftIO $ writeChan (workers ! workerId) GET_INUSE

addToAllWorkers :: [FullClause (At Opaque)] -> Dispatcher ()
addToAllWorkers fcls =
    do n <- fromIntegral <$> (asks workerCount)
       forM_ [0..n-1] $ \workerId -> do
	    addToWorkerMsg (workerId, fcls)

getInUseFromWorkers :: Dispatcher InUseClauseSet
getInUseFromWorkers =
    do n <- (asks workerCount)
       workerChan <- channel fromWorkers
       clauses <- forM [1..n] $ \_ -> do
                      msg <- liftIO $ readChan workerChan
                      case msg of
                       INUSE cls -> return cls
                       NEW _  _  -> do INUSE cls' <- liftIO $ readChan workerChan
                                       return cls'
       let cls = foldl (++) [] clauses
       return $ execState(mapM_ addToInUse cls) newSet


addToInUse ::FullClause (At Opaque) -> State InUseClauseSet ()
addToInUse cl = do iu <- get
                   put $ IU.add cl iu

channel :: (DispatcherChans -> a) -> Dispatcher a
channel f = asks (f . dispatcherChans)
