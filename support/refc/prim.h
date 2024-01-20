#pragma once

#include "cBackend.h"
#if !defined(__STDC_NO_ATOMICS__)
#include <stdatomic.h>
#endif

// IORef

Value *idris2_Data_IORef_prim__newIORef(Value *, Value *, Value *);
#if !defined(__STDC_NO_ATOMICS__) && ATOMIC_POINTER_LOCK_FREE
#define idris2_Data_IORef_prim__readIORef(erased, ioref, world)                \
  (newReference(atomic_load(&((Value_IORef *)ioref)->v)))
#else
#define idris2_Data_IORef_prim__readIORef(erased, ioref, world)                \
  (newReference(((Value_IORef *)iroef)->v)))
#endif

Value *idris2_Data_IORef_prim__writeIORef(Value *, Value *, Value *, Value *);

// Sys

Value *idris2_System_Info_prim__os(void);
Value *idris2_System_Info_prim__codegen(void);
Value *idris2_crash(Value *msg);

// Array

Value *idris2_Data_IOArray_Prims_prim__newArray(Value *, Value *, Value *,
                                                Value *);
#define idris2_Data_IOArray_Prims_prim__arrayGet(rased, array, i, word)        \
  (newReference(((Value_Array *)(array))->arr[((Value_Int64 *)i)->i64]))
Value *idris2_Data_IOArray_Prims_prim__arraySet(Value *, Value *, Value *,
                                                Value *, Value *);

// Pointer
Value *idris2_Prelude_IO_prim__onCollect(Value *, Value *, Value *, Value *);
Value *idris2_Prelude_IO_prim__onCollectAny(Value *, Value *, Value *);

#define idris2_Prelude_Uninhabited_prim__void(x, y) (NULL)

// Threads
Value *System_Concurrency_Raw_prim__mutexRelease(Value *, Value *);

Value *System_Concurrency_Raw_prim__mutexAcquire(Value *, Value *);

Value *System_Concurrency_Raw_prim__makeMutex(Value *);

Value *System_Concurrency_Raw_prim__makeCondition(Value *);

Value *System_Concurrency_Raw_prim__conditionWait(Value *, Value *, Value *);

Value *System_Concurrency_Raw_prim__conditionWaitTimeout(Value *, Value *,
                                                         Value *, Value *);

Value *System_Concurrency_Raw_prim__conditionSignal(Value *, Value *);

Value *System_Concurrency_Raw_prim__conditionBroadcast(Value *, Value *);
