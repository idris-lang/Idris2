#pragma once

#include "cBackend.h"

void idris2_missing_ffi();

int idris2_isUnique(Value *value);
void idris2_removeReuseConstructor(Value_Constructor *constr);

Value *idris2_apply_closure(Value *, Value *arg);
void idris2_push_Arglist(Value_Arglist *arglist, Value *arg);

int idris2_extractInt(Value *);
Value *idris2_trampoline(Value *closure);
Value *idris2_tailcall_apply_closure(Value *_clos, Value *arg);
