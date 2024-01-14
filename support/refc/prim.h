#pragma once

#include "cBackend.h"

// IORef

Value *idris2_Data_IORef_prim__newIORef(Value *, Value *, Value *);
#define idris2_Data_IORef_prim__readIORef(erased, ix, world)                   \
  (newReference(global_IORef_Storage->refs[((Value_IORef *)ix)->index]))

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
