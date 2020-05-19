module Channel

import Linear
import Data.IORef
import Data.List

import System.Concurrency.Raw

public export
data Actions : Type -> Type where
     Send : (a : Type) -> (a -> Actions b) -> Actions b
     Recv : (a : Type) -> (a -> Actions b) -> Actions b
     Close : Actions ()

public export
dual : Actions a -> Actions a
dual (Send x f) = Recv x (\val => dual (f val))
dual (Recv x f) = Send x (\val => dual (f val))
dual Close = Close

public export
data Protocol : Type -> Type where
     Request : (a : Type) -> Protocol a
     Respond : (a : Type) -> Protocol a
     Bind : Protocol a -> (a -> Protocol b) -> Protocol b
     Loop : Inf (Protocol a) -> Protocol a
     Done : Protocol ()

public export
(>>=) : Protocol a -> (a -> Protocol b) -> Protocol b
(>>=) = Bind

public export
ClientK : Protocol a -> (a -> Actions b) -> Actions b
ClientK (Request a) k = Send a k
ClientK (Respond a) k = Recv a k
ClientK (Bind act next) k = ClientK act (\res => ClientK (next res) k)
ClientK (Loop proto) k = ClientK proto k
ClientK Done k = k ()

public export
ServerK : Protocol a -> (a -> Actions b) -> Actions b
ServerK (Request a) k = Recv a k
ServerK (Respond a) k = Send a k
ServerK (Bind act next) k = ServerK act (\res => ServerK (next res) k)
ServerK (Loop proto) k = ServerK proto k
ServerK Done k = k ()

public export
AsClient : Protocol a -> Actions ()
AsClient proto = ClientK proto (\res => Close)

public export
AsServer : Protocol a -> Actions ()
AsServer proto = ServerK proto (\res => Close)

public export
data QueueEntry : Type where
     Entry : (1 val : any) -> QueueEntry

public export
record RawMsgQueue where
  constructor MkRawMsgQueue
  inputStack : List QueueEntry
  outputStack : List QueueEntry

newQueue : RawMsgQueue
newQueue = MkRawMsgQueue [] []

enqueue : (1 val : a) -> RawMsgQueue -> RawMsgQueue
enqueue item q = record { inputStack $= (Entry item ::) } q

dequeue : RawMsgQueue -> Maybe (RawMsgQueue, QueueEntry)
dequeue q
    = case outputStack q of
           [] => case reverse (inputStack q) of
                      [] => Nothing
                      (x :: xs) => Just (record { outputStack = xs, inputStack = [] } q, x)
           (x :: xs) => Just (record { outputStack = xs } q, x)

public export
data Channel : {p : Protocol b} -> Actions a -> Type where
     MkChannel : (lock : Mutex) ->
                 (cond_lock : Mutex) ->
                 (cond : Condition) ->
                 (myInbox : IORef RawMsgQueue) ->
                 (remoteInbox : IORef RawMsgQueue) -> Channel {p} actions

public export
Client : Protocol a -> Type
Client p = Channel {p} (AsClient p)

public export
Server : Protocol a -> Type
Server p = Channel {p} (AsServer p)

mkChannels : (p : Protocol a) -> One IO (Client p, Server p)
mkChannels p
    = do clientInbox <- lift $ newIORef newQueue
         serverInbox <- lift $ newIORef newQueue
         lock <- lift $ makeMutex
         cond_lock <- lift $ makeMutex
         cond <- lift $ makeCondition
         pure (MkChannel lock cond_lock cond clientInbox serverInbox,
               MkChannel lock cond_lock cond serverInbox clientInbox)

export
send : (1 chan : Channel {p} (Send ty next)) -> (1 val : ty) ->
       One IO (Channel {p} (next val))
send (MkChannel lock cond_lock cond local remote) val
    = do lift $ mutexAcquire lock
         q <- lift $ readIORef remote
         lift $ writeIORef remote (enqueue val q)
         lift $ mutexRelease lock

         lift $ mutexAcquire cond_lock
         lift $ conditionSignal cond
         lift $ mutexRelease cond_lock
         pure (MkChannel lock cond_lock cond local remote)

-- returns Nothing if the message isn't there
export
tryRecv : forall b, a .
          {0 ty : Type} ->
          {0 next : (ty -> Actions a)} ->
          {0 p : Protocol b} ->
          (1 chan : Channel {p} (Recv ty next)) ->
          One IO (Res (Maybe ty) (\r => case r of
                                             Nothing => Channel {p} (Recv ty next)
                                             Just val => Channel {p} (next val)))
tryRecv (MkChannel lock cond_lock cond local remote)
    = do lift $ mutexAcquire lock
         rq <- lift $ readIORef local
         case dequeue rq of
              Nothing =>
                  do lift $ mutexRelease lock
                     pure (Nothing @@ MkChannel lock cond_lock cond local remote)
              Just (rq', Entry {any} val) =>
                  do lift $ writeIORef local rq'
                     lift $ mutexRelease lock
                     pure (Just (believe_me {a=any} val) @@
                           MkChannel lock cond_lock cond local remote)

-- blocks until the message is there
export
recv : (1 chan : Channel {p} (Recv ty next)) ->
       One IO (Res ty (\val => Channel {p} (next val)))
recv (MkChannel lock cond_lock cond local remote)
    = do lift $ mutexAcquire lock
         rq <- lift $ readIORef local
         case dequeue rq of
              Nothing => -- ... no message, so wait for condition and try again
                  do lift $ mutexRelease lock
                     lift $ mutexAcquire cond_lock
                     lift $ conditionWait cond cond_lock
                     lift $ mutexRelease cond_lock
                     recv (MkChannel lock cond_lock cond local remote)
              Just (rq', Entry {any} val) =>
                  do lift $ writeIORef local rq'
                     lift $ mutexRelease lock
                     pure (believe_me {a=any} val @@
                           MkChannel lock cond_lock cond local remote)

export
timeoutRecv : forall b, a .
              {0 ty : Type} ->
              {0 next : (ty -> Actions a)} ->
              {0 p : Protocol b} ->
              (1 chan : Channel {p} (Recv ty next)) ->
              (timeout : Int) ->
              One IO (Res (Maybe ty) (\r => case r of
                                                 Nothing => Channel {p} (Recv ty next)
                                                 Just val => Channel {p} (next val)))
timeoutRecv (MkChannel lock cond_lock cond local remote) timeout
    = do lift $ mutexAcquire lock
         rq <- lift $ readIORef local
         case dequeue rq of
              Nothing => -- ... no message, so wait for condition and try again with tryRecv
                  do lift $ mutexRelease lock
                     lift $ mutexAcquire cond_lock
                     lift $ conditionWaitTimeout cond cond_lock timeout
                     lift $ mutexRelease cond_lock
                     res @@ chan <- tryRecv {ty} {next} (MkChannel lock cond_lock cond local remote)
                     case res of
                          Nothing => pure (Nothing @@ chan)
                          Just res => pure (Just res @@ chan)
              Just (rq', Entry {any} val) =>
                  do lift $ writeIORef local rq'
                     lift $ mutexRelease lock
                     pure (Just (believe_me {a=any} val) @@
                           MkChannel lock cond_lock cond local remote)

export
close : (1 chan : Channel Close) -> Any IO ()
close (MkChannel _ _ _ _ _) = pure ()

export
fork : {p : _} -> ((1 chan : Server p) -> Any IO ()) ->
       One IO (Client p)
fork proc
    = do (cchan, MkChannel a b c d e) <- mkChannels p
        -- deconstruct and reconstruct is a hack to work around the fact that
        -- 'run' doesn't express the function is only used once in its type, because
        -- 'Monad' and 'Applicative' don't express linearity... ugh!
         lift $ fork (run (proc (MkChannel a b c d e)))
         pure cchan
