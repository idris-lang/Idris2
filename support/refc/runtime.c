#include "runtime.h"
#include "refc_util.h"

void missing_ffi() {
  fprintf(stderr, "Foreign function declared, but not defined.\n"
                  "Cannot call missing FFI - aborting.\n");
  exit(1);
}

static inline Value *idris2_dispatch_closure(Value_Closure *clo) {
  Value **const xs = clo->args;
  Value *(*const f)() = clo->f;

  switch (clo->arity) {
  default:
    return (*f)(xs);

  case 0:
    return (*f)();
  case 1:
    return (*f)(xs[0]);
  case 2:
    return (*f)(xs[0], xs[1]);
  case 3:
    return (*f)(xs[0], xs[1], xs[2]);
  case 4:
    return (*f)(xs[0], xs[1], xs[2], xs[3]);
  case 5:
    return (*f)(xs[0], xs[1], xs[2], xs[3], xs[4]);
  case 6:
    return (*f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5]);
  case 7:
    return (*f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6]);
  case 8:
    return (*f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6], xs[7]);
  case 9:
    return (*f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6], xs[7], xs[8]);
  case 10:
    return (*f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6], xs[7], xs[8],
                xs[9]);
  case 11:
    return (*f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6], xs[7], xs[8],
                xs[9], xs[10]);
  case 12:
    return (*f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6], xs[7], xs[8],
                xs[9], xs[10], xs[11]);
  case 13:
    return (*f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6], xs[7], xs[8],
                xs[9], xs[10], xs[11], xs[12]);
  case 14:
    return (*f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6], xs[7], xs[8],
                xs[9], xs[10], xs[11], xs[12], xs[13]);
  case 15:
    return (*f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6], xs[7], xs[8],
                xs[9], xs[10], xs[11], xs[12], xs[13], xs[14]);
  case 16:
    return (*f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6], xs[7], xs[8],
                xs[9], xs[10], xs[11], xs[12], xs[13], xs[14], xs[15]);
  }
}

Value *idris2_trampoline(Value *it) {
  while (it && it->header.tag == CLOSURE_TAG) {
    Value_Closure *clos = (Value_Closure *)it;
    if (clos->filled < clos->arity)
      break;

    it = idris2_dispatch_closure(clos);
    if (idris2_isUnique(clos))
      free(clos);
    else
      --clos->header.refCounter;
  }
  return it;
}

Value *idris2_tailcall_apply_closure(Value *_clos, Value *arg) {
  // create a new closure and copy args.
  Value_Closure *clos = (Value_Closure *)_clos;
  Value_Closure *newclos = idris2_makeClosure(
      clos->f, clos->arity, clos->filled + 1 /* expanding a payload */);

  if (clos->header.refCounter <= 1) {
    memcpy(newclos->args, clos->args, sizeof(Value *) * clos->filled);
  } else {
    // if the closure has multiple references, then apply newReference to
    // arguments to avoid premature clearing of arguments
    for (int i = 0; i < clos->filled; ++i)
      newclos->args[i] = newReference(clos->args[i]);
  }
  newclos->args[clos->filled] = arg; // add argument to new arglist

  if (idris2_isUnique(clos)) {
    free(clos);
  } else {
    --clos->header.refCounter;
  }

  return (Value *)newclos;
}

Value *idris2_apply_closure(Value *_clos, Value *arg) {
  return idris2_trampoline(idris2_tailcall_apply_closure(_clos, arg));
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
