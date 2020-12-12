module System.Concurrency.Raw

-- At the moment this is pretty fundamentally tied to the Scheme RTS.
-- Given that different back ends will have entirely different threading
-- models, it might be unavoidable, but we might want to think about possible
-- primitives that back ends should support.


-- Thread mailboxes

%foreign "scheme:blodwen-get-thread-id"
prim__threadID : PrimIO ThreadID
%foreign "scheme:blodwen-set-thread-data"
prim__setThreadData : {a : Type} -> a -> PrimIO ()
%foreign "scheme:blodwen-get-thread-data"
prim__getThreadData : (a : Type) -> PrimIO a


-- Mutexes

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

%foreign "scheme,chez:blodwen-mutex"
prim__makeMutex : PrimIO Mutex
%foreign "scheme,chez:blodwen-lock"
prim__mutexAcquire : Mutex -> PrimIO ()
%foreign "scheme,chez:blodwen-unlock"
prim__mutexRelease : Mutex -> PrimIO ()

||| Creates and returns a new mutex.
export
makeMutex : IO Mutex
makeMutex = primIO prim__makeMutex

||| Acquires the mutex identified by `mutex`. The thread blocks until the mutex
||| has been acquired.
|||
||| Mutexes are recursive in Posix threads terminology, which means that the
||| calling thread can use mutex-acquire to (re)acquire a mutex it already has.
||| In this case, an equal number of mutex-release calls is necessary to release
||| the mutex.
export
mutexAcquire : Mutex -> IO ()
mutexAcquire m = primIO (prim__mutexAcquire m)

||| Releases the mutex identified by `mutex`. Unpredictable behavior results if
||| the mutex is not owned by the calling thread.
export
mutexRelease : Mutex -> IO ()
mutexRelease m = primIO (prim__mutexRelease m)


-- Condition variables

export
data Condition : Type where [external]

%foreign "scheme,chez:blodwen-condition"
prim__makeCondition : PrimIO Condition
%foreign "scheme,chez:blodwen-condition-wait"
prim__conditionWait : Condition -> Mutex -> PrimIO ()
%foreign "scheme,chez:blodwen-condition-wait-timeout"
prim__conditionWaitTimeout : Condition -> Mutex -> Int -> PrimIO ()
%foreign "scheme,chez:blodwen-condition-signal"
prim__conditionSignal : Condition -> PrimIO ()
%foreign "scheme,chez:blodwen-condition-broadcast"
prim__conditionBroadcast : Condition -> PrimIO ()


||| Creates and returns a new condition variable.
export
makeCondition : IO Condition
makeCondition = primIO prim__makeCondition

||| Waits up to the specified timeout for the condition identified by the
||| condition variable `cond`. The calling thread must have acquired the mutex
||| identified by `mutex` at the time `conditionWait` is called. The mutex is
||| released as a side effect of the call to `conditionWait`. When a thread is
||| later released from the condition variable by one of the procedures
||| described below, the mutex is reacquired and `conditionWait` returns.
export
conditionWait : Condition -> Mutex -> IO ()
conditionWait cond mutex = primIO (prim__conditionWait cond mutex)

||| Variant of `conditionWait` with a timeout in microseconds.
||| When the timeout expires, the thread is released, `mutex` is reacquired, and
||| `conditionWaitTimeout` returns.
export
conditionWaitTimeout : Condition -> Mutex -> Int -> IO ()
conditionWaitTimeout cond mutex timeout = primIO (prim__conditionWaitTimeout cond mutex timeout)

||| Releases one of the threads waiting for the condition identified by `cond`.
export
conditionSignal : Condition -> IO ()
conditionSignal c = primIO (prim__conditionSignal c)

||| Releases all of the threads waiting for the condition identified by `cond`.
export
conditionBroadcast : Condition -> IO ()
conditionBroadcast c = primIO (prim__conditionBroadcast c)


--- Semaphores

export
data Semaphore : Type where [external]

%foreign "scheme:blodwen-make-semaphore"
prim__makeSemaphore : Int -> PrimIO Semaphore
%foreign "scheme:blodwen-semaphore-post"
prim__semaphorePost : Semaphore -> PrimIO ()
%foreign "scheme:blodwen-semaphore-wait"
prim__semaphoreWait : Semaphore -> PrimIO ()


||| Creates and returns a new semaphore with the counter initially set to `init`.
export
makeSemaphore : Int -> IO Semaphore
makeSemaphore init = primIO (prim__makeSemaphore init)

||| Increments the semaphore's internal counter.
export
semaphorePost : Semaphore -> IO ()
semaphorePost sema = primIO (prim__semaphorePost sema)

||| Blocks until the internal counter for semaphore sema is non-zero. When the
||| counter is non-zero, it is decremented and `semaphoreWait` returns.
export
semaphoreWait : Semaphore -> IO ()
semaphoreWait sema = primIO (prim__semaphoreWait sema)
