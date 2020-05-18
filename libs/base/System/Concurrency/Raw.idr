module System.Concurrency.Raw

-- At the moment this is pretty fundamentally tied to the Scheme RTS
-- Given that different back ends will have entirely different threading
-- models, it might be unavoidable, but we might want to think about possible
-- primitives that back ends should support.

%foreign "scheme:blodwen-thisthread"
prim__threadID : PrimIO ThreadID
%foreign "scheme:blodwen-set-thread-data"
prim__setThreadData : {a : Type} -> a -> PrimIO ()
%foreign "scheme:blodwen-get-thread-data"
prim__getThreadData : (a : Type) -> PrimIO a

-- Mutexes and condition variables.

export
threadID : IO ThreadID
threadID = primIO prim__threadID

export
setThreadData : {a : Type} -> a -> IO ()
setThreadData val = primIO (prim__setThreadData val)

export
getThreadData : (a : Type) -> IO a
getThreadData a = primIO (prim__getThreadData a)

export
data Mutex : Type where [external]

%foreign "scheme:blodwen-mutex"
prim__makeMutex : PrimIO Mutex
%foreign "scheme:blodwen-lock"
prim__mutexAcquire : Mutex -> PrimIO ()
%foreign "scheme:blodwen-unlock"
prim__mutexRelease : Mutex -> PrimIO ()

export
makeMutex : IO Mutex
makeMutex = primIO prim__makeMutex

export
mutexAcquire : Mutex -> IO ()
mutexAcquire m = primIO (prim__mutexAcquire m)

export
mutexRelease : Mutex -> IO ()
mutexRelease m = primIO (prim__mutexRelease m)

export
data Condition : Type where [external]

%foreign "scheme:blodwen-condition"
prim__makeCondition : PrimIO Condition
%foreign "scheme:blodwen-condition-wait"
prim__conditionWait : Condition -> Mutex -> PrimIO ()
%foreign "scheme:blodwen-condition-wait-timoue"
prim__conditionWaitTimeout : Condition -> Mutex -> Int -> PrimIO ()
%foreign "scheme:blodwen-condition-signal"
prim__conditionSignal : Condition -> PrimIO ()
%foreign "scheme:blodwen-condition-broadcast"
prim__conditionBroadcast : Condition -> PrimIO ()

export
makeCondition : IO Condition
makeCondition = primIO prim__makeCondition

export
conditionWait : Condition -> Mutex -> IO ()
conditionWait c m = primIO (prim__conditionWait c m)

export
conditionWaitTimeout : Condition -> Mutex -> Int -> IO ()
conditionWaitTimeout c m t = primIO (prim__conditionWaitTimeout c m t)

export
conditionSignal : Condition -> IO ()
conditionSignal c = primIO (prim__conditionSignal c)

export
conditionBroadcast : Condition -> IO ()
conditionBroadcast c = primIO (prim__conditionBroadcast c)
