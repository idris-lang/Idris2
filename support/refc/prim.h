#ifndef __PRIM_H__
#define __PRIM_H__

#include "cBackend.h"



// Value * Prelude_IO_prim__putStr(Value *, Value *);
Value *Prelude_IO_prim__getChar(Value *);

// IORef

Value *newIORef(Value *, Value *, Value *);
Value *readIORef(Value *, Value *, Value *);
Value *writeIORef(Value *, Value *, Value *, Value *);

// Sys

Value *sysOS(void);
Value* idris2_crash(Value* msg);

// Array

Value *newArray(Value *, Value *, Value *, Value *);
Value *arrayGet(Value *, Value *, Value *, Value *);
Value *arraySet(Value *, Value *, Value *, Value *, Value *);

// Pointer
Value *PrimIO_prim__nullAnyPtr(Value *);

Value *onCollect(Value *, Value *, Value *, Value *);
Value *onCollectAny(Value *, Value *, Value *, Value *);

Value *voidElim(Value *, Value *);

// Threads
Value *System_Concurrency_Raw_prim__mutexRelease(Value *, Value *);

Value *System_Concurrency_Raw_prim__mutexAcquire(Value *, Value *);

Value *System_Concurrency_Raw_prim__makeMutex(Value *);

Value *System_Concurrency_Raw_prim__makeCondition(Value *);

Value *System_Concurrency_Raw_prim__conditionWait(Value *, Value *, Value *);

Value *System_Concurrency_Raw_prim__conditionWaitTimeout(Value *, Value *, Value *, Value *);

Value *System_Concurrency_Raw_prim__conditionSignal(Value *, Value *);

Value *System_Concurrency_Raw_prim__conditionBroadcast(Value *, Value *);
#endif
