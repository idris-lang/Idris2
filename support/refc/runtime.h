#pragma once

#include "cBackend.h"

void idris2_missing_ffi();

#define idris2_isUnique(x) ((x)->header.refCounter == 1)
void idris2_removeReuseConstructor(Value_Constructor *constr);

Value *idris2_apply_closure(Value *, Value *arg);
Value *idris2_tailcall_apply_closure(Value *_clos, Value *arg);
Value *idris2_trampoline(Value *closure);

int idris2_extractInt(Value *);
