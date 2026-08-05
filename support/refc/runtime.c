#include "runtime.h"
#include "_datatypes.h"
#include "refc_util.h"

void idris2_missing_ffi() {
  fprintf(stderr, "Foreign function declared, but not defined.\n"
                  "Cannot call missing FFI - aborting.\n");
  exit(1);
}

typedef Idris2_Value *(*const FUN0)();
typedef Idris2_Value *(*const FUN1)(Idris2_Value *);
typedef Idris2_Value *(*const FUN2)(Idris2_Value *, Idris2_Value *);
typedef Idris2_Value *(*const FUN3)(Idris2_Value *, Idris2_Value *,
                                    Idris2_Value *);
typedef Idris2_Value *(*const FUN4)(Idris2_Value *, Idris2_Value *,
                                    Idris2_Value *, Idris2_Value *);
typedef Idris2_Value *(*const FUN5)(Idris2_Value *, Idris2_Value *,
                                    Idris2_Value *, Idris2_Value *,
                                    Idris2_Value *);
typedef Idris2_Value *(*const FUN6)(Idris2_Value *, Idris2_Value *,
                                    Idris2_Value *, Idris2_Value *,
                                    Idris2_Value *, Idris2_Value *);
typedef Idris2_Value *(*const FUN7)(Idris2_Value *, Idris2_Value *,
                                    Idris2_Value *, Idris2_Value *,
                                    Idris2_Value *, Idris2_Value *,
                                    Idris2_Value *);
typedef Idris2_Value *(*const FUN8)(Idris2_Value *, Idris2_Value *,
                                    Idris2_Value *, Idris2_Value *,
                                    Idris2_Value *, Idris2_Value *,
                                    Idris2_Value *, Idris2_Value *);
typedef Idris2_Value *(*const FUN9)(Idris2_Value *, Idris2_Value *,
                                    Idris2_Value *, Idris2_Value *,
                                    Idris2_Value *, Idris2_Value *,
                                    Idris2_Value *, Idris2_Value *,
                                    Idris2_Value *);
typedef Idris2_Value *(*const FUN10)(Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *);
typedef Idris2_Value *(*const FUN11)(Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *);
typedef Idris2_Value *(*const FUN12)(Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *);
typedef Idris2_Value *(*const FUN13)(Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *);
typedef Idris2_Value *(*const FUN14)(Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *,
                                     Idris2_Value *, Idris2_Value *);
typedef Idris2_Value *(*const FUN15)(
    Idris2_Value *, Idris2_Value *, Idris2_Value *, Idris2_Value *,
    Idris2_Value *, Idris2_Value *, Idris2_Value *, Idris2_Value *,
    Idris2_Value *, Idris2_Value *, Idris2_Value *, Idris2_Value *,
    Idris2_Value *, Idris2_Value *, Idris2_Value *);
typedef Idris2_Value *(*const FUN16)(
    Idris2_Value *, Idris2_Value *, Idris2_Value *, Idris2_Value *,
    Idris2_Value *, Idris2_Value *, Idris2_Value *, Idris2_Value *,
    Idris2_Value *, Idris2_Value *, Idris2_Value *, Idris2_Value *,
    Idris2_Value *, Idris2_Value *, Idris2_Value *, Idris2_Value *);
typedef Idris2_Value *(*const FUNStar)(Idris2_Value **);

static inline Idris2_Value *idris2_dispatch_closure(Idris2_Closure *clo) {
  Idris2_Value **const xs = clo->args;

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

Idris2_Value *idris2_trampoline(Idris2_Value *it) {
  while (it && !idris2_vp_is_unboxed(it) && it->header.tag == CLOSURE_TAG) {
    Idris2_Closure *clos = (Idris2_Closure *)it;
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

Idris2_Value *idris2_tailcall_apply_closure(Idris2_Value *_clos,
                                            Idris2_Value *arg) {
  // create a new closure and copy args.
  Idris2_Closure *clos = (Idris2_Closure *)_clos;
  Idris2_Closure *newclos = idris2_mkClosure(
      clos->f, clos->arity, clos->filled + 1 /* expanding a payload */);

  if (clos->header.refCounter <= 1) {
    memcpy(newclos->args, clos->args, sizeof(Idris2_Value *) * clos->filled);
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

  return (Idris2_Value *)newclos;
}

Idris2_Value *idris2_apply_closure(Idris2_Value *_clos, Idris2_Value *arg) {
  return idris2_trampoline(idris2_tailcall_apply_closure(_clos, arg));
}

void idris2_removeReuseConstructor(Idris2_Constructor *constr) {
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

int idris2_extractInt(Idris2_Value *v) {
  if (idris2_vp_is_unboxed(v))
    return (int)((uintptr_t)(v) >> idris2_vp_int_shift);

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
    return (int)mpz_get_si(((Idris2_Integer *)v)->i);
  case DOUBLE_TAG:
    return (int)idris2_vp_to_Double(v);
  default:
    return -1;
  }
}
