#include "runtime.h"
#include "_datatypes.h"
#include "refc_util.h"

void idris2_missing_ffi() {
  fprintf(stderr, "Foreign function declared, but not defined.\n"
                  "Cannot call missing FFI - aborting.\n");
  exit(1);
}

typedef Value *(*const FUN0)();
typedef Value *(*const FUN1)(Value *);
typedef Value *(*const FUN2)(Value *, Value *);
typedef Value *(*const FUN3)(Value *, Value *, Value *);
typedef Value *(*const FUN4)(Value *, Value *, Value *, Value *);
typedef Value *(*const FUN5)(Value *, Value *, Value *, Value *, Value *);
typedef Value *(*const FUN6)(Value *, Value *, Value *, Value *, Value *,
                             Value *);
typedef Value *(*const FUN7)(Value *, Value *, Value *, Value *, Value *,
                             Value *, Value *);
typedef Value *(*const FUN8)(Value *, Value *, Value *, Value *, Value *,
                             Value *, Value *, Value *);
typedef Value *(*const FUN9)(Value *, Value *, Value *, Value *, Value *,
                             Value *, Value *, Value *, Value *);
typedef Value *(*const FUN10)(Value *, Value *, Value *, Value *, Value *,
                              Value *, Value *, Value *, Value *, Value *);
typedef Value *(*const FUN11)(Value *, Value *, Value *, Value *, Value *,
                              Value *, Value *, Value *, Value *, Value *,
                              Value *);
typedef Value *(*const FUN12)(Value *, Value *, Value *, Value *, Value *,
                              Value *, Value *, Value *, Value *, Value *,
                              Value *, Value *);
typedef Value *(*const FUN13)(Value *, Value *, Value *, Value *, Value *,
                              Value *, Value *, Value *, Value *, Value *,
                              Value *, Value *, Value *);
typedef Value *(*const FUN14)(Value *, Value *, Value *, Value *, Value *,
                              Value *, Value *, Value *, Value *, Value *,
                              Value *, Value *, Value *, Value *);
typedef Value *(*const FUN15)(Value *, Value *, Value *, Value *, Value *,
                              Value *, Value *, Value *, Value *, Value *,
                              Value *, Value *, Value *, Value *, Value *);
typedef Value *(*const FUN16)(Value *, Value *, Value *, Value *, Value *,
                              Value *, Value *, Value *, Value *, Value *,
                              Value *, Value *, Value *, Value *, Value *,
                              Value *);
typedef Value *(*const FUNStar)(Value **);

static inline Value *idris2_dispatch_closure(Value_Closure *clo) {
  Value **const xs = clo->args;

  switch (clo->arity) {
  default:
    return (*(FUNStar)clo->f)(xs);

  case 0:
    return (*(FUN0)clo->f)();
  case 1:
    return (*(FUN1)clo->f)(xs[0]);
  case 2:
    return (*(FUN2)clo->f)(xs[0], xs[1]);
  case 3:
    return (*(FUN3)clo->f)(xs[0], xs[1], xs[2]);
  case 4:
    return (*(FUN4)clo->f)(xs[0], xs[1], xs[2], xs[3]);
  case 5:
    return (*(FUN5)clo->f)(xs[0], xs[1], xs[2], xs[3], xs[4]);
  case 6:
    return (*(FUN6)clo->f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5]);
  case 7:
    return (*(FUN7)clo->f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6]);
  case 8:
    return (*(FUN8)clo->f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6],
                           xs[7]);
  case 9:
    return (*(FUN9)clo->f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6],
                           xs[7], xs[8]);
  case 10:
    return (*(FUN10)clo->f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6],
                            xs[7], xs[8], xs[9]);
  case 11:
    return (*(FUN11)clo->f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6],
                            xs[7], xs[8], xs[9], xs[10]);
  case 12:
    return (*(FUN12)clo->f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6],
                            xs[7], xs[8], xs[9], xs[10], xs[11]);
  case 13:
    return (*(FUN13)clo->f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6],
                            xs[7], xs[8], xs[9], xs[10], xs[11], xs[12]);
  case 14:
    return (*(FUN14)clo->f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6],
                            xs[7], xs[8], xs[9], xs[10], xs[11], xs[12],
                            xs[13]);
  case 15:
    return (*(FUN15)clo->f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6],
                            xs[7], xs[8], xs[9], xs[10], xs[11], xs[12], xs[13],
                            xs[14]);
  case 16:
    return (*(FUN16)clo->f)(xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6],
                            xs[7], xs[8], xs[9], xs[10], xs[11], xs[12], xs[13],
                            xs[14], xs[15]);
  }
}

Value *idris2_trampoline(Value *it) {
  while (it && !idris2_vp_is_unboxed(it) && it->header.tag == CLOSURE_TAG) {
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
  Value_Closure *newclos = idris2_mkClosure(
      clos->f, clos->arity, clos->filled + 1 /* expanding a payload */);

  if (clos->header.refCounter <= 1) {
    memcpy(newclos->args, clos->args, sizeof(Value *) * clos->filled);
  } else {
    // if the closure has multiple references, then apply newReference to
    // arguments to avoid premature clearing of arguments
    for (int i = 0; i < clos->filled; ++i)
      newclos->args[i] = idris2_newReference(clos->args[i]);
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
