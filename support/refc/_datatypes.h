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
} Value_header;
#define IDRIS2_STOCKVAL(t)                                                     \
  { IDRIS2_VP_REFCOUNTER_MAX, t, 0 }

typedef struct {
  Value_header header;
  // `Value` is an "abstract" struct,
  // `Value_Xxx` structs have the same header
  // followed by type-specific payload.
} Value;

/*
We expect at least 4 bytes for `Value_header` alignment, to use bit0 and bit1 of
pointer as flags.

RefC does not have complete static tracking of type information, so types are
identified at runtime using Value_Header's tag field. However, Int that are
pretending to be pointers cannot have that tag, so use that flag to identify
them first. Of course, this flag is not used if it is clear that Value* is
actually an Int. But places like newReference/removeReference require this flag.
 */
#define idris2_vp_is_unboxed(p) ((uintptr_t)(p)&3)

#define idris2_vp_int_shift                                                    \
  ((sizeof(uintptr_t) >= 8 && sizeof(Value *) >= 8) ? 32 : 16)

#define idris2_vp_to_Bits64(p) (((Value_Bits64 *)(p))->ui64)

#if !defined(UINTPTR_WIDTH)
#define idris2_vp_to_Bits32(p)                                                 \
  ((idris2_vp_int_shift == 16)                                                 \
       ? (((Value_Bits32 *)(p))->ui32)                                         \
       : ((uint32_t)((uintptr_t)(p) >> idris2_vp_int_shift)))
#define idris2_vp_to_Int32(p)                                                  \
  ((idris2_vp_int_shift == 16)                                                 \
       ? (((Value_Int32 *)(p))->i32)                                           \
       : ((int32_t)((uintptr_t)(p) >> idris2_vp_int_shift)))

#elif UINTPTR_WIDTH >= 64
// NOTE: We stole two bits from pointer. So, even if we have 64-bit CPU,
//  Int64/Bits654 are not unboxable.
#define idris2_vp_to_Bits32(p)                                                 \
  ((uint32_t)((uintptr_t)(p) >> idris2_vp_int_shift))
#define idris2_vp_to_Int32(p) ((int32_t)((uintptr_t)(p) >> idris2_vp_int_shift))

#elif UINTPTR_WIDTH >= 32
#define idris2_vp_to_Bits32(p) (((Value_Bits32 *)(p))->ui32)
#define idris2_vp_to_Int32(p) (((Value_Int32 *)(p))->i32)

#else
#error "unsupported uintptr_t width"
#endif

#define idris2_vp_to_Bits16(p)                                                 \
  ((uint16_t)((uintptr_t)(p) >> idris2_vp_int_shift))
#define idris2_vp_to_Bits8(p) ((uint8_t)((uintptr_t)(p) >> idris2_vp_int_shift))
#define idris2_vp_to_Int64(p) (((Value_Int64 *)(p))->i64)
#define idris2_vp_to_Int16(p) ((int16_t)((uintptr_t)(p) >> idris2_vp_int_shift))
#define idris2_vp_to_Int8(p) ((int8_t)((uintptr_t)(p) >> idris2_vp_int_shift))
#define idris2_vp_to_Char(p)                                                   \
  ((unsigned char)((uintptr_t)(p) >> idris2_vp_int_shift))
#define idris2_vp_to_Double(p) (((Value_Double *)(p))->d)
#define idris2_vp_to_Bool(p) (idris2_vp_to_Int8(p))

typedef struct {
  Value_header header;
  uint32_t ui32;
} Value_Bits32;

typedef struct {
  Value_header header;
  uint64_t ui64;
} Value_Bits64;

typedef struct {
  Value_header header;
  int32_t i32;
} Value_Int32;

typedef struct {
  Value_header header;
  int64_t i64;
} Value_Int64;

typedef struct {
  Value_header header;
  mpz_t i;
} Value_Integer;

typedef struct {
  Value_header header;
  double d;
} Value_Double;

typedef struct {
  Value_header header;
  char *str;
} Value_String;

typedef struct {
  Value_header header;
  int32_t total;
  int32_t tag;
  char const *name;
  Value *args[];
} Value_Constructor;

typedef struct {
  Value_header header;
  // function type depends on arity, see idris2_dispatch_closure
  void *f;
  uint8_t arity;
  uint8_t filled; // length of args.
  Value *args[];
} Value_Closure;

typedef struct {
  Value_header header;
  Value *v;
} Value_IORef;

typedef struct {
  Value_header header;
  void *p;
} Value_Pointer;

typedef struct {
  Value_header header;
  Value_Pointer *p;
  Value_Closure *onCollectFct;
} Value_GCPointer;

typedef struct {
  Value_header header;
  int capacity;
  Value **arr;
} Value_Array;

typedef struct {
  Value_header header;
  Buffer *buffer;
} Value_Buffer;

typedef struct {
  Value_header header;
  pthread_mutex_t *mutex;
} Value_Mutex;

typedef struct {
  Value_header header;
  pthread_cond_t *cond;
} Value_Condition;

void idris2_dumpMemoryStats(void);
