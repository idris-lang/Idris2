#include "runtime.h"
#include "refc_util.h"

void idris2_missing_ffi() {
  fprintf(stderr, "Foreign function declared, but not defined.\n"
                  "Cannot call missing FFI - aborting.\n");
  exit(1);
}

void idris2_push_Arglist(Value_Arglist *arglist, Value *arg) {
  IDRIS2_REFC_VERIFY(arglist->filled < arglist->total,
                     "unable to add more arguments to arglist");

  arglist->args[arglist->filled] = idris2_newReference(arg);
  arglist->filled++;
}

int idris2_isUnique(Value *value) {
  if (value) {
    return value->header.refCounter == 1;
  }
  return 0;
}

// necessary because not every variable passed as arguments is duplicated
void idris2_deconstructArglist(Value_Arglist *arglist) {
  IDRIS2_REFC_VERIFY(arglist->header.refCounter > 0, "refCounter %lld",
                     (long long)arglist->header.refCounter);
  arglist->header.refCounter--;
  if (arglist->header.refCounter == 0) {
    free(arglist->args);
    free(arglist);
  }
}

void idris2_deconstructClosure(Value_Closure *clos) {
  IDRIS2_REFC_VERIFY(clos->header.refCounter > 0, "refCounter %lld",
                     (long long)clos->header.refCounter);
  clos->header.refCounter--;
  if (clos->header.refCounter == 0) {
    idris2_deconstructArglist(clos->arglist);
    free(clos);
  }
}

void idris2_removeReuseConstructor(Value_Constructor *constr) {
  if (!constr) {
    return;
  }
  IDRIS2_REFC_VERIFY(constr->header.refCounter > 0, "refCounter %lld",
                     (long long)constr->header.refCounter);
  constr->header.refCounter--;
  if (constr->header.refCounter == 0) {
    free(constr);
  }
}

Value_Arglist *idris2_makeArglistToApplyClosure(Value *_clos, Value *arg) {
  // create a new arg list
  Value_Arglist *oldArgs = ((Value_Closure *)_clos)->arglist;
  Value_Arglist *newArgs = idris2_newArglist(0, oldArgs->total);
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
      newArgs->args[i] = idris2_newReference(oldArgs->args[i]);
  }
  newArgs->args[oldArgs->filled] = arg;
  return newArgs;
}

Value *idris2_apply_closure(Value *_clos, Value *arg) {
  Value_Arglist *newArgs = idris2_makeArglistToApplyClosure(_clos, arg);

  Value_Closure *clos = (Value_Closure *)_clos;
  fun_ptr_t f = clos->f;

  idris2_deconstructClosure(clos);

  // check if enough arguments exist
  if (newArgs->filled >= newArgs->total) {
    while (1) {
      Value *retVal = f(newArgs);
      idris2_deconstructArglist(newArgs);
      if (!retVal || idris2_vp_is_unboxed(retVal) ||
          retVal->header.tag != COMPLETE_CLOSURE_TAG) {
        return retVal;
      }
      f = ((Value_Closure *)retVal)->f;
      newArgs = ((Value_Closure *)retVal)->arglist;
      newArgs = (Value_Arglist *)idris2_newReference((Value *)newArgs);
      idris2_removeReference(retVal);
    }
  }

  return (Value *)idris2_makeClosureFromArglist(f, newArgs);
}

Value *idris2_tailcall_apply_closure(Value *_clos, Value *arg) {
  Value_Arglist *newArgs = idris2_makeArglistToApplyClosure(_clos, arg);

  Value_Closure *clos = (Value_Closure *)_clos;
  fun_ptr_t f = ((Value_Closure *)clos)->f;

  idris2_deconstructClosure(clos);

  return (Value *)idris2_makeClosureFromArglist(f, newArgs);
}

int idris2_extractInt(Value *v) {
  if (idris2_vp_is_unboxed(v))
    return (int)idris2_vp_to_Int32(v);

  switch (v->header.tag) {
  case BITS32_TAG:
    return (int)idris2_vp_to_Bits32(v);
  case BITS64_TAG:
    return (int)idris2_vp_to_Bits64(v);
  case INT32_TAG:
    return (int)idris2_vp_to_Bits32(v);
  case INT64_TAG:
    return (int)idris2_vp_to_Int64(v);
  case INTEGER_TAG:
    return (int)mpz_get_si(((Value_Integer *)v)->i);
  case DOUBLE_TAG:
    return (int)idris2_vp_to_Double(v);
  default:
    return -1;
  }
}

Value *idris2_trampoline(Value *closure) {
  if (!closure || idris2_vp_is_unboxed(closure))
    return closure;

  fun_ptr_t f = ((Value_Closure *)closure)->f;
  Value_Arglist *_arglist = ((Value_Closure *)closure)->arglist;
  Value_Arglist *arglist =
      (Value_Arglist *)idris2_newReference((Value *)_arglist);
  idris2_removeReference(closure);
  while (1) {
    Value *retVal = f(arglist);
    idris2_deconstructArglist(arglist);
    if (!retVal || idris2_vp_is_unboxed(retVal) ||
        retVal->header.tag != COMPLETE_CLOSURE_TAG) {
      return retVal;
    }
    f = ((Value_Closure *)retVal)->f;
    arglist = ((Value_Closure *)retVal)->arglist;
    arglist = (Value_Arglist *)idris2_newReference((Value *)arglist);
    idris2_removeReference(retVal);
  }
  return NULL;
}
