#include "runtime.h"
#include "refc_util.h"

void missing_ffi() {
  fprintf(stderr, "Foreign function declared, but not defined.\n"
                  "Cannot call missing FFI - aborting.\n");
  exit(1);
}

void push_Arglist(Value_Arglist *arglist, Value *arg) {
  IDRIS2_REFC_VERIFY(arglist->filled < arglist->total,
                     "unable to add more arguments to arglist");

  arglist->args[arglist->filled] = newReference(arg);
  arglist->filled++;
}

int isUnique(Value *value) {
  if (value) {
    return value->header.refCounter == 1;
  }
  return 0;
}

// necessary because not every variable passed as arguments is duplicated
void deconstructArglist(Value_Arglist *arglist) {
  IDRIS2_REFC_VERIFY(arglist->header.refCounter > 0, "refCounter %lld",
                     (long long)arglist->header.refCounter);
  arglist->header.refCounter--;
  if (arglist->header.refCounter == 0) {
    free(arglist->args);
    free(arglist);
  }
}

void deconstructClosure(Value_Closure *clos) {
  IDRIS2_REFC_VERIFY(clos->header.refCounter > 0, "refCounter %lld",
                     (long long)clos->header.refCounter);
  clos->header.refCounter--;
  if (clos->header.refCounter == 0) {
    deconstructArglist(clos->arglist);
    free(clos);
  }
}

void removeReuseConstructor(Value_Constructor *constr) {
  if (!constr) {
    return;
  }
  IDRIS2_REFC_VERIFY(constr->header.refCounter > 0, "refCounter %lld",
                     (long long)constr->header.refCounter);
  constr->header.refCounter--;
  if (constr->header.refCounter == 0) {
    if (constr->name) {
      free(constr->name);
    }
    free(constr->args);
    free(constr);
  }
}

Value_Arglist *makeArglistToApplyClosure(Value *_clos, Value *arg) {
  // create a new arg list
  Value_Arglist *oldArgs = ((Value_Closure *)_clos)->arglist;
  Value_Arglist *newArgs = newArglist(0, oldArgs->total);
  newArgs->filled = oldArgs->filled + 1;
  // add argument to new arglist
  for (int i = 0; i < oldArgs->filled; i++) {
    /*
    if the closure has multiple references, then apply newReference to arguments
    to avoid premature clearing of arguments
    */
    if (_clos->header.refCounter <= 1)
      newArgs->args[i] = oldArgs->args[i];
    else
      newArgs->args[i] = newReference(oldArgs->args[i]);
  }
  newArgs->args[oldArgs->filled] = arg;
  return newArgs;
}

Value *apply_closure(Value *_clos, Value *arg) {
  Value_Arglist *newArgs = makeArglistToApplyClosure(_clos, arg);

  Value_Closure *clos = (Value_Closure *)_clos;
  fun_ptr_t f = clos->f;

  deconstructClosure(clos);

  // check if enough arguments exist
  if (newArgs->filled >= newArgs->total) {
    while (1) {
      Value *retVal = f(newArgs);
      deconstructArglist(newArgs);
      if (!retVal || retVal->header.tag != COMPLETE_CLOSURE_TAG) {
        return retVal;
      }
      f = ((Value_Closure *)retVal)->f;
      newArgs = ((Value_Closure *)retVal)->arglist;
      newArgs = (Value_Arglist *)newReference((Value *)newArgs);
      removeReference(retVal);
    }
  }

  return (Value *)makeClosureFromArglist(f, newArgs);
}

Value *tailcall_apply_closure(Value *_clos, Value *arg) {
  Value_Arglist *newArgs = makeArglistToApplyClosure(_clos, arg);

  Value_Closure *clos = (Value_Closure *)_clos;
  fun_ptr_t f = ((Value_Closure *)clos)->f;

  deconstructClosure(clos);

  return (Value *)makeClosureFromArglist(f, newArgs);
}

int extractInt(Value *v) {
  switch (v->header.tag) {
  case BITS8_TAG:
    return (int)((Value_Bits8 *)v)->ui8;
  case BITS16_TAG:
    return (int)((Value_Bits16 *)v)->ui16;
  case BITS32_TAG:
    return (int)((Value_Bits32 *)v)->ui32;
  case BITS64_TAG:
    return (int)((Value_Bits64 *)v)->ui64;
  case INT8_TAG:
    return (int)((Value_Int8 *)v)->i8;
  case INT16_TAG:
    return (int)((Value_Int16 *)v)->i16;
  case INT32_TAG:
    return (int)((Value_Int32 *)v)->i32;
  case INT64_TAG:
    return (int)((Value_Int64 *)v)->i64;
  case INTEGER_TAG:
    return (int)mpz_get_si(((Value_Integer *)v)->i);
  case DOUBLE_TAG:
    return (int)((Value_Double *)v)->d;
  case CHAR_TAG:
    return (int)((Value_Char *)v)->c;
  default:
    return -1;
  }
}

Value *trampoline(Value *closure) {
  fun_ptr_t f = ((Value_Closure *)closure)->f;
  Value_Arglist *_arglist = ((Value_Closure *)closure)->arglist;
  Value_Arglist *arglist = (Value_Arglist *)newReference((Value *)_arglist);
  removeReference(closure);
  while (1) {
    Value *retVal = f(arglist);
    deconstructArglist(arglist);
    if (!retVal || retVal->header.tag != COMPLETE_CLOSURE_TAG) {
      return retVal;
    }
    f = ((Value_Closure *)retVal)->f;
    arglist = ((Value_Closure *)retVal)->arglist;
    arglist = (Value_Arglist *)newReference((Value *)arglist);
    removeReference(retVal);
  }
  return NULL;
}
