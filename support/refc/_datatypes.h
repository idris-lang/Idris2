#pragma once

#include <gmp.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "buffer.h"

#define NO_TAG 0
#define BITS32_TAG 3
#define BITS64_TAG 4
#define INT32_TAG 7
#define INT64_TAG 8
#define INTEGER_TAG 9
#define DOUBLE_TAG 10
#define STRING_TAG 12

#define CLOSURE_TAG 15
#define CONSTRUCTOR_TAG 17

#define IOREF_TAG 20
#define ARRAY_TAG 21
#define POINTER_TAG 22
#define GC_POINTER_TAG 23
#define BUFFER_TAG 24

#define MUTEX_TAG 30
#define CONDITION_TAG 31

typedef struct {
  // Objects that reach the maximum reference count will be immortalized.
  // This 'immortalization' feature is also utilized to prevent statically
  // allocated objects from being destroyed.
#define IDRIS2_VP_REFCOUNTER_MAX UINT16_MAX
  uint16_t refCounter;
  uint8_t tag;
  uint8_t reserved;
} Idris2_header;
#define IDRIS2_STOCKVAL(t)                                                     \
  { IDRIS2_VP_REFCOUNTER_MAX, t, 0 }

typedef struct {
  Idris2_header header;
  // `Idris2_Value` is an "abstract" struct,
  // `Value_Xxx` structs have the same header
  // followed by type-specific payload.
} Idris2_Value;

/*
We expect at least 4 bytes for `Idris2_header` alignment, to use bit0 and bit1
of pointer as flags.

RefC does not have complete static tracking of type information, so types are
identified at runtime using Idris2_header's tag field. However, Int that are
pretending to be pointers cannot have that tag, so use that flag to identify
them first. Of course, this flag is not used if it is clear that Idris2_Value*
is actually an Int. But places like newReference/removeReference require this
flag.
 */
#define idris2_vp_is_unboxed(p) ((uintptr_t)(p)&3)

#define idris2_vp_int_shift                                                    \
  ((sizeof(uintptr_t) >= 8 && sizeof(Idris2_Value *) >= 8) ? 32 : 16)

#define idris2_vp_to_Bits64(p) (((Idris2_Bits64 *)(p))->ui64)

#if !defined(UINTPTR_WIDTH)
#define idris2_vp_to_Bits32(p)                                                 \
  ((idris2_vp_int_shift == 16)                                                 \
       ? (((Idris2_Bits32 *)(p))->ui32)                                        \
       : ((uint32_t)((uintptr_t)(p) >> idris2_vp_int_shift)))
#define idris2_vp_to_Int32(p)                                                  \
  ((idris2_vp_int_shift == 16)                                                 \
       ? (((Idris2_Int32 *)(p))->i32)                                          \
       : ((int32_t)((uintptr_t)(p) >> idris2_vp_int_shift)))

#elif UINTPTR_WIDTH >= 64
// NOTE: We stole two bits from pointer. So, even if we have 64-bit CPU,
//  Int64/Bits654 are not unboxable.
#define idris2_vp_to_Bits32(p)                                                 \
  ((uint32_t)((uintptr_t)(p) >> idris2_vp_int_shift))
#define idris2_vp_to_Int32(p) ((int32_t)((uintptr_t)(p) >> idris2_vp_int_shift))

#elif UINTPTR_WIDTH >= 32
#define idris2_vp_to_Bits32(p) (((Idris2_Bits32 *)(p))->ui32)
#define idris2_vp_to_Int32(p) (((Idris2_Int32 *)(p))->i32)

#else
#error "unsupported uintptr_t width"
#endif

#define idris2_vp_to_Bits16(p)                                                 \
  ((uint16_t)((uintptr_t)(p) >> idris2_vp_int_shift))
#define idris2_vp_to_Bits8(p) ((uint8_t)((uintptr_t)(p) >> idris2_vp_int_shift))
#define idris2_vp_to_Int64(p) (((Idris2_Int64 *)(p))->i64)
#define idris2_vp_to_Int16(p) ((int16_t)((uintptr_t)(p) >> idris2_vp_int_shift))
#define idris2_vp_to_Int8(p) ((int8_t)((uintptr_t)(p) >> idris2_vp_int_shift))
#define idris2_vp_to_Char(p)                                                   \
  ((unsigned char)((uintptr_t)(p) >> idris2_vp_int_shift))
#define idris2_vp_to_Double(p) (((Idris2_Double *)(p))->d)
#define idris2_vp_to_Bool(p) (idris2_vp_to_Int8(p))

typedef struct {
  Idris2_header header;
  uint32_t ui32;
} Idris2_Bits32;

typedef struct {
  Idris2_header header;
  uint64_t ui64;
} Idris2_Bits64;

typedef struct {
  Idris2_header header;
  int32_t i32;
} Idris2_Int32;

typedef struct {
  Idris2_header header;
  int64_t i64;
} Idris2_Int64;

typedef struct {
  Idris2_header header;
  mpz_t i;
} Idris2_Integer;

typedef struct {
  Idris2_header header;
  double d;
} Idris2_Double;

typedef struct {
  Idris2_header header;
  char *str;
} Idris2_String;

typedef struct {
  Idris2_header header;
  int32_t total;
  int32_t tag;
  char const *name;
  Idris2_Value *args[];
} Idris2_Constructor;

typedef struct {
  Idris2_header header;
  // function type depends on arity, see idris2_dispatch_closure
  void *f;
  uint8_t arity;
  uint8_t filled; // length of args.
  Idris2_Value *args[];
} Idris2_Closure;

typedef struct {
  Idris2_header header;
  Idris2_Value *v;
} Idris2_IORef;

typedef struct {
  Idris2_header header;
  void *p;
} Idris2_Pointer;

typedef struct {
  Idris2_header header;
  Idris2_Pointer *p;
  Idris2_Closure *onCollectFct;
} Idris2_GCPointer;

typedef struct {
  Idris2_header header;
  int capacity;
  Idris2_Value **arr;
} Idris2_Array;

typedef struct {
  Idris2_header header;
  Buffer *buffer;
} Idris2_Buffer;

typedef struct {
  Idris2_header header;
  pthread_mutex_t *mutex;
} Idris2_Mutex;

typedef struct {
  Idris2_header header;
  pthread_cond_t *cond;
} Idris2_Condition;

void idris2_dumpMemoryStats(void);
