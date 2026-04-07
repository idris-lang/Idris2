#pragma once

#include "cBackend.h"

// IORef

Idris2_Value *idris2_Data_IORef_prim__newIORef(Idris2_Value *, Idris2_Value *,
                                               Idris2_Value *);
#define idris2_Data_IORef_prim__readIORef(erased, ioref, world)                \
  (idris2_newReference(((Idris2_IORef *)ioref)->v))

Idris2_Value *idris2_Data_IORef_prim__writeIORef(Idris2_Value *, Idris2_Value *,
                                                 Idris2_Value *,
                                                 Idris2_Value *);

// Sys

extern Idris2_String const idris2_predefined_osstring;
extern Idris2_String const idris2_predefined_codegenstring;
#define idris2_System_Info_prim__os()                                          \
  ((Idris2_Value *)&idris2_predefined_osstring)
#define idris2_System_Info_prim__codegen()                                     \
  ((Idris2_Value *)&idris2_predefined_codegenstring)
Idris2_Value *idris2_crash(Idris2_Value *msg);

// Array

Idris2_Value *idris2_Data_IOArray_Prims_prim__newArray(Idris2_Value *,
                                                       Idris2_Value *,
                                                       Idris2_Value *,
                                                       Idris2_Value *);
#define idris2_Data_IOArray_Prims_prim__arrayGet(rased, array, i, word)        \
  (idris2_newReference(((Idris2_Array *)(array))->arr[idris2_vp_to_Int64(i)]))
Idris2_Value *idris2_Data_IOArray_Prims_prim__arraySet(Idris2_Value *,
                                                       Idris2_Value *,
                                                       Idris2_Value *,
                                                       Idris2_Value *,
                                                       Idris2_Value *);

// Pointer
Idris2_Value *idris2_Prelude_IO_prim__onCollect(Idris2_Value *, Idris2_Value *,
                                                Idris2_Value *, Idris2_Value *);
Idris2_Value *idris2_Prelude_IO_prim__onCollectAny(Idris2_Value *,
                                                   Idris2_Value *,
                                                   Idris2_Value *);

// Threads
Idris2_Value *System_Concurrency_Raw_prim__mutexRelease(Idris2_Value *,
                                                        Idris2_Value *);

Idris2_Value *System_Concurrency_Raw_prim__mutexAcquire(Idris2_Value *,
                                                        Idris2_Value *);

Idris2_Value *System_Concurrency_Raw_prim__makeMutex(Idris2_Value *);

Idris2_Value *System_Concurrency_Raw_prim__makeCondition(Idris2_Value *);

Idris2_Value *System_Concurrency_Raw_prim__conditionWait(Idris2_Value *,
                                                         Idris2_Value *,
                                                         Idris2_Value *);

Idris2_Value *System_Concurrency_Raw_prim__conditionWaitTimeout(Idris2_Value *,
                                                                Idris2_Value *,
                                                                Idris2_Value *,
                                                                Idris2_Value *);

Idris2_Value *System_Concurrency_Raw_prim__conditionSignal(Idris2_Value *,
                                                           Idris2_Value *);

Idris2_Value *System_Concurrency_Raw_prim__conditionBroadcast(Idris2_Value *,
                                                              Idris2_Value *);

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
