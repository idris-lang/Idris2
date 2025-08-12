#pragma once

#include "cBackend.h"

// IORef

Value *idris2_Data_IORef_prim__newIORef(Value *, Value *, Value *);
#define idris2_Data_IORef_prim__readIORef(erased, ioref, world)                \
  (idris2_newReference(((Value_IORef *)ioref)->v))

Value *idris2_Data_IORef_prim__writeIORef(Value *, Value *, Value *, Value *);

// Sys

extern Value_String const idris2_predefined_osstring;
extern Value_String const idris2_predefined_codegenstring;
#define idris2_System_Info_prim__os() ((Value *)&idris2_predefined_osstring)
#define idris2_System_Info_prim__codegen()                                     \
  ((Value *)&idris2_predefined_codegenstring)
Value *idris2_crash(Value *msg);

// Array

Value *idris2_Data_IOArray_Prims_prim__newArray(Value *, Value *, Value *,
                                                Value *);
#define idris2_Data_IOArray_Prims_prim__arrayGet(rased, array, i, word)        \
  (idris2_newReference(((Value_Array *)(array))->arr[idris2_vp_to_Int64(i)]))
Value *idris2_Data_IOArray_Prims_prim__arraySet(Value *, Value *, Value *,
                                                Value *, Value *);

// Pointer
Value *idris2_Prelude_IO_prim__onCollect(Value *, Value *, Value *, Value *);
Value *idris2_Prelude_IO_prim__onCollectAny(Value *, Value *, Value *);

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

extern char const idris2_constr_Int[];
extern char const idris2_constr_Int8[];
extern char const idris2_constr_Int16[];
extern char const idris2_constr_Int32[];
extern char const idris2_constr_Int64[];
extern char const idris2_constr_Bits8[];
extern char const idris2_constr_Bits16[];
extern char const idris2_constr_Bits32[];
extern char const idris2_constr_Bits64[];
extern char const idris2_constr_Double[];
extern char const idris2_constr_Integer[];
extern char const idris2_constr_Char[];
extern char const idris2_constr_String[];
extern char const idris2_constr____gt[];
