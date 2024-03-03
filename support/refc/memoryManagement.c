#include <stdbool.h>

#include "_datatypes.h"
#include "refc_util.h"
#include "runtime.h"

#if 0
struct {
  unsigned int n_newValue;
  unsigned int n_newReference;
  unsigned int n_actualNewReference;
  unsigned int n_immortalized;
  unsigned int n_removeReference;
  unsigned int n_tried_to_kill_immortals;
  unsigned int n_freed;
} idris2_memory_stat = {0, 0, 0, 0, 0, 00, 0};
#define IDRIS2_INC_MEMSTAT(x)                                                  \
  do {                                                                         \
    ++(idris2_memory_stat.x);                                                  \
  } while (0)

void idris2_dumpMemoryStats(void) {
  fprintf(
      stderr,
      "n_newValue = %u\n"
      "n_newReference = %u\n"
      "n_actualNewReference = %u\n"
      "n_immortalized = %u\n"
      "n_removeReference = %u\n"
      "n_tried_to_kill_immortals = %u\n"
      "n_freed = %u\n",
      idris2_memory_stat.n_newValue, idris2_memory_stat.n_newReference,
      idris2_memory_stat.n_actualNewReference,
      idris2_memory_stat.n_immortalized, idris2_memory_stat.n_removeReference,
      idris2_memory_stat.n_tried_to_kill_immortals, idris2_memory_stat.n_freed);
}

#else
#define IDRIS2_INC_MEMSTAT(x)
// don't inline this, Because IDRIS2_MEMSTAT works only at compiling support
// libralies to suppressing overhead.
void idris2_dumpMemoryStats() {}
#endif

Value *newValue(size_t size) {
  Value *retVal = (Value *)malloc(size);
  IDRIS2_REFC_VERIFY(retVal, "malloc failed");
  IDRIS2_INC_MEMSTAT(n_newValue);
  retVal->header.refCounter = 1;
  retVal->header.tag = NO_TAG;
  return retVal;
}

Value_Arglist *newArglist(int missing, int total) {
  Value_Arglist *retVal = IDRIS2_NEW_VALUE(Value_Arglist);
  retVal->header.tag = ARGLIST_TAG;
  retVal->total = total;
  retVal->filled = total - missing;
  retVal->args = (Value **)malloc(sizeof(Value *) * total);
  memset(retVal->args, 0, sizeof(Value *) * total);
  return retVal;
}

Value_Constructor *newConstructor(int total, int tag) {
  Value_Constructor *retVal = (Value_Constructor *)newValue(
      sizeof(Value_Constructor) + sizeof(Value *) * total);
  retVal->header.tag = CONSTRUCTOR_TAG;
  retVal->total = total;
  retVal->tag = tag;
  retVal->name = NULL;
  return retVal;
}

Value_Closure *makeClosureFromArglist(fun_ptr_t f, Value_Arglist *arglist) {
  Value_Closure *retVal = IDRIS2_NEW_VALUE(Value_Closure);
  retVal->header.tag = CLOSURE_TAG;
  retVal->arglist = arglist; // (Value_Arglist *)newReference((Value*)arglist);
  retVal->f = f;
  if (retVal->arglist->filled >= retVal->arglist->total) {
    retVal->header.tag = COMPLETE_CLOSURE_TAG;
  }
  return retVal;
}

Value_Double *makeDouble(double d) {
  Value_Double *retVal = IDRIS2_NEW_VALUE(Value_Double);
  retVal->header.tag = DOUBLE_TAG;
  retVal->d = d;
  return retVal;
}

Value_Char *makeChar(char c) {
  Value_Char *retVal = IDRIS2_NEW_VALUE(Value_Char);
  retVal->header.tag = CHAR_TAG;
  retVal->c = c;
  return retVal;
}

Value_Bits8 *makeBits8(uint8_t i) {
  Value_Bits8 *retVal = IDRIS2_NEW_VALUE(Value_Bits8);
  retVal->header.tag = BITS8_TAG;
  retVal->ui8 = i;
  return retVal;
}

Value_Bits16 *makeBits16(uint16_t i) {
  Value_Bits16 *retVal = IDRIS2_NEW_VALUE(Value_Bits16);
  retVal->header.tag = BITS16_TAG;
  retVal->ui16 = i;
  return retVal;
}

Value_Bits32 *makeBits32(uint32_t i) {
  Value_Bits32 *retVal = IDRIS2_NEW_VALUE(Value_Bits32);
  retVal->header.tag = BITS32_TAG;
  retVal->ui32 = i;
  return retVal;
}

Value_Bits64 *makeBits64(uint64_t i) {
  if (i < 100)
    return &idris2_predefined_Bits64[i];

  Value_Bits64 *retVal = IDRIS2_NEW_VALUE(Value_Bits64);
  retVal->header.tag = BITS64_TAG;
  retVal->ui64 = i;
  return retVal;
}

Value_Int8 *makeInt8(int8_t i) {
  Value_Int8 *retVal = IDRIS2_NEW_VALUE(Value_Int8);
  retVal->header.tag = INT8_TAG;
  retVal->i8 = i;
  return retVal;
}

Value_Int16 *makeInt16(int16_t i) {
  Value_Int16 *retVal = IDRIS2_NEW_VALUE(Value_Int16);
  retVal->header.tag = INT16_TAG;
  retVal->i16 = i;
  return retVal;
}

Value_Int32 *makeInt32(int32_t i) {
  Value_Int32 *retVal = IDRIS2_NEW_VALUE(Value_Int32);
  retVal->header.tag = INT32_TAG;
  retVal->i32 = i;
  return retVal;
}

Value_Int64 *makeInt64(int64_t i) {
  if (i >= 0 && i < 100)
    return &idris2_predefined_Int64[i];

  Value_Int64 *retVal = IDRIS2_NEW_VALUE(Value_Int64);
  retVal->header.tag = INT64_TAG;
  retVal->i64 = i;
  return retVal;
}

Value_Int8 *makeBool(int p) { return makeInt8(p ? 1 : 0); }

Value_Integer *makeInteger() {
  Value_Integer *retVal = IDRIS2_NEW_VALUE(Value_Integer);
  retVal->header.tag = INTEGER_TAG;
  mpz_init(retVal->i);
  return retVal;
}

Value_Integer *makeIntegerLiteral(char *i) {
  Value_Integer *retVal = makeInteger();
  mpz_set_str(retVal->i, i, 10);
  return retVal;
}

Value_String *makeEmptyString(size_t l) {
  if (l == 1)
    return &idris2_predefined_nullstring;

  Value_String *retVal = IDRIS2_NEW_VALUE(Value_String);
  retVal->header.tag = STRING_TAG;
  retVal->str = malloc(l);
  memset(retVal->str, 0, l);
  return retVal;
}

Value_String *makeString(char *s) {
  if (s[0] == '\0')
    return &idris2_predefined_nullstring;

  Value_String *retVal = IDRIS2_NEW_VALUE(Value_String);
  int l = strlen(s);
  retVal->header.tag = STRING_TAG;
  retVal->str = malloc(l + 1);
  memset(retVal->str, 0, l + 1);
  memcpy(retVal->str, s, l);
  return retVal;
}

Value_Pointer *makePointer(void *ptr_Raw) {
  Value_Pointer *p = IDRIS2_NEW_VALUE(Value_Pointer);
  p->header.tag = POINTER_TAG;
  p->p = ptr_Raw;
  return p;
}

Value_GCPointer *makeGCPointer(void *ptr_Raw, Value_Closure *onCollectFct) {
  Value_GCPointer *p = IDRIS2_NEW_VALUE(Value_GCPointer);
  p->header.tag = GC_POINTER_TAG;
  p->p = makePointer(ptr_Raw);
  p->onCollectFct = onCollectFct;
  return p;
}

Value_Buffer *makeBuffer(void *buf) {
  Value_Buffer *b = IDRIS2_NEW_VALUE(Value_Buffer);
  b->header.tag = BUFFER_TAG;
  b->buffer = buf;
  return b;
}

Value_Array *makeArray(int length) {
  Value_Array *a = IDRIS2_NEW_VALUE(Value_Array);
  a->header.tag = ARRAY_TAG;
  a->capacity = length;
  a->arr = (Value **)malloc(sizeof(Value *) * length);
  memset(a->arr, 0, sizeof(Value *) * length);
  return a;
}

Value *newReference(Value *source) {
  IDRIS2_INC_MEMSTAT(n_newReference);

  // note that we explicitly allow NULL as source (for erased arguments)
  if (source && source->header.refCounter != IDRIS2_VP_REFCOUNTER_MAX) {
    IDRIS2_INC_MEMSTAT(n_actualNewReference);
    ++source->header.refCounter;
    if (source->header.refCounter == IDRIS2_VP_REFCOUNTER_MAX)
      IDRIS2_INC_MEMSTAT(n_immortalized);
  }
  return source;
}

void removeReference(Value *elem) {
  IDRIS2_INC_MEMSTAT(n_removeReference);
  if (!elem)
    return;
  if (elem->header.refCounter == IDRIS2_VP_REFCOUNTER_MAX) {
    IDRIS2_INC_MEMSTAT(n_tried_to_kill_immortals);
    return;
  }

  // remove reference counter
  elem->header.refCounter--;
  if (elem->header.refCounter == 0)
  // recursively remove all references to all children
  {
    IDRIS2_INC_MEMSTAT(n_freed);

    switch (elem->header.tag) {
    case BITS8_TAG:
    case BITS16_TAG:
    case BITS32_TAG:
    case BITS64_TAG:
    case INT8_TAG:
    case INT16_TAG:
    case INT32_TAG:
    case INT64_TAG:
      /* nothing to delete, added for sake of completeness */
      break;
    case INTEGER_TAG: {
      mpz_clear(((Value_Integer *)elem)->i);
      break;
    }
    case DOUBLE_TAG:
      /* nothing to delete, added for sake of completeness */
      break;
    case CHAR_TAG:
      /* nothing to delete, added for sake of completeness */
      break;
    case STRING_TAG:
      free(((Value_String *)elem)->str);
      break;

    case CLOSURE_TAG: {
      Value_Closure *cl = (Value_Closure *)elem;
      Value_Arglist *al = cl->arglist;
      removeReference((Value *)al);
      break;
    }
    case COMPLETE_CLOSURE_TAG: {
      Value_Closure *cl = (Value_Closure *)elem;
      Value_Arglist *al = cl->arglist;
      removeReference((Value *)al);
      break;
    }
    case ARGLIST_TAG: {
      Value_Arglist *al = (Value_Arglist *)elem;
      for (int i = 0; i < al->filled; i++) {
        removeReference(al->args[i]);
      }
      free(al->args);
      break;
    }
    case CONSTRUCTOR_TAG: {
      Value_Constructor *constr = (Value_Constructor *)elem;
      for (int i = 0; i < constr->total; i++) {
        removeReference(constr->args[i]);
      }
      break;
    }
    case IOREF_TAG:
      removeReference(((Value_IORef *)elem)->v);
      break;

    case BUFFER_TAG: {
      Value_Buffer *b = (Value_Buffer *)elem;
      free(b->buffer);
      break;
    }

    case ARRAY_TAG: {
      Value_Array *a = (Value_Array *)elem;
      for (int i = 0; i < a->capacity; i++) {
        removeReference(a->arr[i]);
      }
      free(a->arr);
      break;
    }
    case POINTER_TAG:
      /* nothing to delete, added for sake of completeness */
      break;

    case GC_POINTER_TAG: {
      /* maybe here we need to invoke onCollectAny */
      Value_GCPointer *vPtr = (Value_GCPointer *)elem;
      Value *closure1 =
          apply_closure((Value *)vPtr->onCollectFct, (Value *)vPtr->p);
      apply_closure(closure1, NULL);
      removeReference((Value *)vPtr->p);
      break;
    }

    default:
      break;
    }
    // finally, free element
    free(elem);
  }
}

// /////////////////////////////////////////////////////////////////////////
// PRE-DEFINED VLAUES

#define IDRIS2_MK_PREDEFINED_INT_10(t, n)                                      \
  {IDRIS2_STOCKVAL(t), (n + 0)}, {IDRIS2_STOCKVAL(t), (n + 1)},                \
      {IDRIS2_STOCKVAL(t), (n + 2)}, {IDRIS2_STOCKVAL(t), (n + 3)},            \
      {IDRIS2_STOCKVAL(t), (n + 4)}, {IDRIS2_STOCKVAL(t), (n + 5)},            \
      {IDRIS2_STOCKVAL(t), (n + 6)}, {IDRIS2_STOCKVAL(t), (n + 7)},            \
      {IDRIS2_STOCKVAL(t), (n + 8)}, {                                         \
    IDRIS2_STOCKVAL(t), (n + 9)                                                \
  }
Value_Int64 idris2_predefined_Int64[100] = {
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 0),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 10),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 20),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 30),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 40),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 50),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 60),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 70),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 80),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 90)};

Value_Bits64 idris2_predefined_Bits64[100] = {
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 0),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 10),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 20),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 30),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 40),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 50),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 60),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 70),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 80),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 90)};

Value_String idris2_predefined_nullstring = {IDRIS2_STOCKVAL(STRING_TAG), ""};

static bool idris2_predefined_integer_initialized = false;
Value_Integer idris2_predefined_Integer[100];
Value *idris2_getPredefinedInteger(int n) {
  IDRIS2_REFC_VERIFY(n >= 0 && n < 100,
                     "invalid range of predefined integers.");

  if (!idris2_predefined_integer_initialized) {
    idris2_predefined_integer_initialized = true;
    for (int i = 0; i < 100; ++i) {
      idris2_predefined_Integer[i].header.refCounter = IDRIS2_VP_REFCOUNTER_MAX;
      idris2_predefined_Integer[i].header.tag = INTEGER_TAG;
      idris2_predefined_Integer[i].header.reserved = 0;

      mpz_init(idris2_predefined_Integer[i].i);
      mpz_set_si(idris2_predefined_Integer[i].i, i);
    }
  }
  return (Value *)&idris2_predefined_Integer[n];
}

