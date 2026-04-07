#pragma once

#include "cBackend.h"

Idris2_Value *idris2_newValue(size_t size);
Idris2_Value *idris2_newReference(Idris2_Value *source);
void idris2_removeReference(Idris2_Value *source);

#define IDRIS2_NEW_VALUE(t) ((t *)idris2_newValue(sizeof(t)))

Idris2_Constructor *idris2_newConstructor(int total, int tag);
Idris2_Closure *idris2_mkClosure(Idris2_Value *(*f)(), uint8_t arity,
                                 uint8_t filled);

Idris2_Value *idris2_mkDouble(double d);
#define idris2_mkChar(x)                                                       \
  ((Idris2_Value *)(((uintptr_t)(x) << idris2_vp_int_shift) + 1))
#define idris2_mkBits8(x)                                                      \
  ((Idris2_Value *)(((uintptr_t)(x) << idris2_vp_int_shift) + 1))
#define idris2_mkBits16(x)                                                     \
  ((Idris2_Value *)(((uintptr_t)(x) << idris2_vp_int_shift) + 1))

#if !defined(UINTPTR_WIDTH)
#define idris2_mkBits32(x)                                                     \
  ((idris2_vp_int_shift == 16)                                                 \
       ? (idris2_mkBits32_Boxed(x))                                            \
       : ((Idris2_Value *)(((uintptr_t)(x) << idris2_vp_int_shift) + 1)))
#define idris2_mkInt32(x)                                                      \
  ((idris2_vp_int_shift == 16)                                                 \
       ? (idris2_mkInt32_Boxed(x))                                             \
       : ((Idris2_Value *)(((uintptr_t)(x) << idris2_vp_int_shift) + 1)))

#elif UINTPTR_WIDTH >= 64
#define idris2_mkBits32(x)                                                     \
  ((Idris2_Value *)(((uintptr_t)(x) << idris2_vp_int_shift) + 1))
#define idris2_mkInt32(x)                                                      \
  ((Idris2_Value *)(((uintptr_t)(x) << idris2_vp_int_shift) + 1))

#elif UINTPTR_WIDTH >= 32
#define idris2_mkBits32(x) (idris2_mkBits32_Boxed(x))
#define idris2_mkInt32(x) (idris2_mkInt32_Boxed(x)))

#else
#error "unsupported uintptr_t width"
#endif

#define idris2_mkInt8(x)                                                       \
  ((Idris2_Value *)(((uintptr_t)(x) << idris2_vp_int_shift) + 1))
#define idris2_mkInt16(x)                                                      \
  ((Idris2_Value *)(((uintptr_t)(x) << idris2_vp_int_shift) + 1))
#define idris2_mkBool(x) (idris2_mkInt8(x))

Idris2_Value *idris2_mkBits32_Boxed(uint32_t i);
Idris2_Value *idris2_mkBits64(uint64_t i);
Idris2_Value *idris2_mkInt32_Boxed(int32_t i);
Idris2_Value *idris2_mkInt64(int64_t i);

Idris2_Integer *idris2_mkInteger();
Idris2_Value *idris2_mkIntegerLiteral(char *i);
Idris2_String *idris2_mkEmptyString(size_t l);
Idris2_String *idris2_mkString(char *);

Idris2_Pointer *idris2_makePointer(void *);
Idris2_GCPointer *idris2_makeGCPointer(void *ptr_Raw,
                                       Idris2_Closure *onCollectFct);
Idris2_Buffer *idris2_makeBuffer(void *buf);
Idris2_Array *idris2_makeArray(int length);

extern Idris2_Int64 const idris2_predefined_Int64[100];
extern Idris2_Bits64 const idris2_predefined_Bits64[100];
extern Idris2_Integer idris2_predefined_Integer[100];
Idris2_Value *idris2_getPredefinedInteger(int n);
extern Idris2_String const idris2_predefined_nullstring;

// You need uncomment a debugging code in memoryManagement.c to use this.
void idris2_dumpMemoryStats(void);
