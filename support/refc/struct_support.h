#pragma once

/* RefC struct-field descriptor and runtime registry.
 *
 * When Idris code uses CFStruct ("point" [("x", Int32), ...]) the codegen
 * emits a static `idris2_struct_t` descriptor for each struct type, plus a
 * call to `idris2_register_struct` in `main()` before any Idris code runs.
 * `prim__getField` / `prim__setField` look up the descriptor at runtime.
 */

#include "memoryManagement.h"
#include <stddef.h>

/* Field kind: mirrors the CFType used in the Idris FFI declaration.
 * IDRIS2_FIELD_INT   — int64_t  (Idris Int)
 * IDRIS2_FIELD_INT32 — int32_t  (Idris Int32)
 * …etc.
 * IDRIS2_FIELD_PTR   — void *   (Idris Ptr t / AnyPtr)
 * IDRIS2_FIELD_STRUCT — void *  (Idris Struct, field holds pointer to nested struct)
 */
typedef enum {
  IDRIS2_FIELD_INT,
  IDRIS2_FIELD_INT8,
  IDRIS2_FIELD_INT16,
  IDRIS2_FIELD_INT32,
  IDRIS2_FIELD_INT64,
  IDRIS2_FIELD_BITS8,
  IDRIS2_FIELD_BITS16,
  IDRIS2_FIELD_BITS32,
  IDRIS2_FIELD_BITS64,
  IDRIS2_FIELD_DOUBLE,
  IDRIS2_FIELD_CHAR,
  IDRIS2_FIELD_STRING,
  IDRIS2_FIELD_PTR,
  IDRIS2_FIELD_STRUCT,
} idris2_field_kind_t;

typedef struct {
  const char         *name;
  size_t              offset;
  idris2_field_kind_t kind;
  const char         *struct_name; /* non-NULL only for IDRIS2_FIELD_STRUCT */
} idris2_field_t;

typedef struct {
  const char      *name;
  idris2_field_t  *fields; /* sentinel-terminated: last entry has name==NULL */
  int              nfields;
  size_t           size;
} idris2_struct_t;

/* Register a struct descriptor.  Call once per struct type before any
 * Idris code runs.  Descriptors are stored in a singly-linked list. */
void idris2_register_struct(idris2_struct_t *desc);

/* External primitives called by generated Idris glue code. */
Value *idris2_prim__getField(Value *struct_name, Value *_e1, Value *_e2,
                              Value *struct_ptr,  Value *field_name,
                              Value *_proof);

Value *idris2_prim__setField(Value *struct_name, Value *_e1, Value *_e2,
                              Value *struct_ptr,  Value *field_name,
                              Value *_proof,
                              Value *val,         Value *_world);
