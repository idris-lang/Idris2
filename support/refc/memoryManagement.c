#include "refc_util.h"
#include "runtime.h"

Value *newValue(size_t size) {
  Value *retVal = (Value *)malloc(size);
  IDRIS2_REFC_VERIFY(retVal, "malloc failed");
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

Value *idris2_mkDouble(double d) {
  Value_Double *retVal = IDRIS2_NEW_VALUE(Value_Double);
  retVal->header.tag = DOUBLE_TAG;
  retVal->d = d;
  return (Value *)retVal;
}

Value *idris2_mkBits32_Boxed(uint32_t i) {
  Value_Bits32 *retVal = IDRIS2_NEW_VALUE(Value_Bits32);
  retVal->header.tag = BITS32_TAG;
  retVal->ui32 = i;
  return (Value *)retVal;
}

Value *idris2_mkBits64(uint64_t i) {
  Value_Bits64 *retVal = IDRIS2_NEW_VALUE(Value_Bits64);
  retVal->header.tag = BITS64_TAG;
  retVal->ui64 = i;
  return (Value *)retVal;
}

Value *idris2_mkInt32_Boxed(int32_t i) {
  Value_Int32 *retVal = IDRIS2_NEW_VALUE(Value_Int32);
  retVal->header.tag = INT32_TAG;
  retVal->i32 = i;
  return (Value *)retVal;
}

Value *idris2_mkInt64(int64_t i) {
  Value_Int64 *retVal = IDRIS2_NEW_VALUE(Value_Int64);
  retVal->header.tag = INT64_TAG;
  retVal->i64 = i;
  return (Value *)retVal;
}

Value_Integer *idris2_mkInteger() {
  Value_Integer *retVal = IDRIS2_NEW_VALUE(Value_Integer);
  retVal->header.tag = INTEGER_TAG;
  mpz_init(retVal->i);
  return retVal;
}

Value_Integer *idris2_mkIntegerLiteral(char *i) {
  Value_Integer *retVal = idris2_mkInteger();
  mpz_set_str(retVal->i, i, 10);
  return retVal;
}

Value_String *idris2_mkEmptyString(size_t l) {
  Value_String *retVal = IDRIS2_NEW_VALUE(Value_String);
  retVal->header.tag = STRING_TAG;
  retVal->str = malloc(l);
  memset(retVal->str, 0, l);
  return retVal;
}

Value_String *idris2_mkString(char *s) {
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
  // note that we explicitly allow NULL as source (for erased arguments)
  if (source && !idris2_vp_is_unboxed(source)) {
    source->header.refCounter++;
  }
  return source;
}

void removeReference(Value *elem) {
  if (!elem || idris2_vp_is_unboxed(elem)) {
    return;
  }

  IDRIS2_REFC_VERIFY(elem->header.refCounter > 0, "refCounter %lld",
                     (long long)elem->header.refCounter);
  // remove reference counter
  elem->header.refCounter--;
  if (elem->header.refCounter == 0)
  // recursively remove all references to all children
  {
    switch (elem->header.tag) {
    case BITS32_TAG:
    case BITS64_TAG:
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
