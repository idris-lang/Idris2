#include "struct_support.h"
#include "refc_util.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* -----------------------------------------------------------------------
 * Registry — a singly-linked list of struct descriptors.
 * ----------------------------------------------------------------------- */

typedef struct registry_entry {
  idris2_struct_t      *desc;
  struct registry_entry *next;
} registry_entry_t;

static registry_entry_t *idris2_struct_registry = NULL;

void idris2_register_struct(idris2_struct_t *desc) {
  registry_entry_t *entry = (registry_entry_t *)malloc(sizeof(registry_entry_t));
  IDRIS2_REFC_VERIFY(entry, "idris2_register_struct: malloc failed");
  entry->desc = desc;
  entry->next = idris2_struct_registry;
  idris2_struct_registry = entry;
}

static idris2_struct_t *idris2_find_struct(const char *name) {
  for (registry_entry_t *e = idris2_struct_registry; e; e = e->next)
    if (strcmp(e->desc->name, name) == 0) return e->desc;
  return NULL;
}

/* -----------------------------------------------------------------------
 * Field get / set helpers
 * ----------------------------------------------------------------------- */

static Value *idris2_struct_get_field(idris2_struct_t *desc,
                                      void *ptr,
                                      const char *fname) {
  for (int i = 0; i < desc->nfields; i++) {
    if (strcmp(desc->fields[i].name, fname) != 0) continue;
    char *base = (char *)ptr + desc->fields[i].offset;
    switch (desc->fields[i].kind) {
    case IDRIS2_FIELD_INT:    return idris2_mkInt64(*(int64_t *)base);
    case IDRIS2_FIELD_INT8:   return idris2_mkInt8(*(int8_t *)base);
    case IDRIS2_FIELD_INT16:  return idris2_mkInt16(*(int16_t *)base);
    case IDRIS2_FIELD_INT32:  return idris2_mkInt32(*(int32_t *)base);
    case IDRIS2_FIELD_INT64:  return idris2_mkInt64(*(int64_t *)base);
    case IDRIS2_FIELD_BITS8:  return idris2_mkBits8(*(uint8_t *)base);
    case IDRIS2_FIELD_BITS16: return idris2_mkBits16(*(uint16_t *)base);
    case IDRIS2_FIELD_BITS32: return idris2_mkBits32(*(uint32_t *)base);
    case IDRIS2_FIELD_BITS64: return idris2_mkBits64(*(uint64_t *)base);
    case IDRIS2_FIELD_DOUBLE: return idris2_mkDouble(*(double *)base);
    case IDRIS2_FIELD_CHAR:   return idris2_mkChar(*(uint32_t *)base);
    case IDRIS2_FIELD_STRING: return (Value *)idris2_mkString(*(char **)base);
    case IDRIS2_FIELD_PTR:
    case IDRIS2_FIELD_STRUCT: return (Value *)idris2_makePointer(*(void **)base);
    }
  }
  fprintf(stderr, "ERROR: prim__getField: unknown field '%s' in struct '%s'\n",
          fname, desc->name);
  exit(1);
}

static void idris2_struct_set_field(idris2_struct_t *desc,
                                     void *ptr,
                                     const char *fname,
                                     Value *val) {
  for (int i = 0; i < desc->nfields; i++) {
    if (strcmp(desc->fields[i].name, fname) != 0) continue;
    char *base = (char *)ptr + desc->fields[i].offset;
    switch (desc->fields[i].kind) {
    case IDRIS2_FIELD_INT:
    case IDRIS2_FIELD_INT64:  *(int64_t *)base  = idris2_vp_to_Int64(val);  return;
    case IDRIS2_FIELD_INT8:   *(int8_t *)base   = idris2_vp_to_Int8(val);   return;
    case IDRIS2_FIELD_INT16:  *(int16_t *)base  = idris2_vp_to_Int16(val);  return;
    case IDRIS2_FIELD_INT32:  *(int32_t *)base  = idris2_vp_to_Int32(val);  return;
    case IDRIS2_FIELD_BITS8:  *(uint8_t *)base  = idris2_vp_to_Bits8(val);  return;
    case IDRIS2_FIELD_BITS16: *(uint16_t *)base = idris2_vp_to_Bits16(val); return;
    case IDRIS2_FIELD_BITS32: *(uint32_t *)base = idris2_vp_to_Bits32(val); return;
    case IDRIS2_FIELD_BITS64: *(uint64_t *)base = idris2_vp_to_Bits64(val); return;
    case IDRIS2_FIELD_DOUBLE: *(double *)base   = idris2_vp_to_Double(val); return;
    case IDRIS2_FIELD_CHAR:   *(uint32_t *)base = idris2_vp_to_Char(val);   return;
    case IDRIS2_FIELD_STRING: *(char **)base    = ((Value_String *)val)->str; return;
    case IDRIS2_FIELD_PTR:
    case IDRIS2_FIELD_STRUCT: *(void **)base    = ((Value_Pointer *)val)->p; return;
    }
  }
  fprintf(stderr, "ERROR: prim__setField: unknown field '%s' in struct '%s'\n",
          fname, desc->name);
  exit(1);
}

/* -----------------------------------------------------------------------
 * External primitives — called from generated Idris glue
 * arg layout matches the Named CExp for GetField / SetField:
 *   getField: [struct_name, _erased, _erased, struct_ptr, field_name, _proof]
 *   setField: [struct_name, _erased, _erased, struct_ptr, field_name, _proof, val, _world]
 * ----------------------------------------------------------------------- */

Value *idris2_prim__getField(Value *struct_name,
                              Value *IDRIS2_UNUSED _e1,
                              Value *IDRIS2_UNUSED _e2,
                              Value *struct_ptr,
                              Value *field_name,
                              Value *IDRIS2_UNUSED _proof) {
  const char *sname = ((Value_String *)struct_name)->str;
  const char *fname = ((Value_String *)field_name)->str;
  void *raw = ((Value_Pointer *)struct_ptr)->p;
  idris2_struct_t *desc = idris2_find_struct(sname);
  IDRIS2_REFC_VERIFY(desc, "prim__getField: unknown struct '%s'", sname);
  return idris2_struct_get_field(desc, raw, fname);
}

Value *idris2_prim__setField(Value *struct_name,
                              Value *IDRIS2_UNUSED _e1,
                              Value *IDRIS2_UNUSED _e2,
                              Value *struct_ptr,
                              Value *field_name,
                              Value *IDRIS2_UNUSED _proof,
                              Value *val,
                              Value *IDRIS2_UNUSED _world) {
  const char *sname = ((Value_String *)struct_name)->str;
  const char *fname = ((Value_String *)field_name)->str;
  void *raw = ((Value_Pointer *)struct_ptr)->p;
  idris2_struct_t *desc = idris2_find_struct(sname);
  IDRIS2_REFC_VERIFY(desc, "prim__setField: unknown struct '%s'", sname);
  idris2_struct_set_field(desc, raw, fname, val);
  return NULL;
}
