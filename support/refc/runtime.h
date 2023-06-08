#pragma once

#include "cBackend.h"

void missing_ffi();

void removeReuseConstructor(Value_Constructor *constr);

Value *apply_closure(Value *, Value *arg);
void push_Arglist(Value_Arglist *arglist, Value *arg);

int extractInt(Value *);
Value *trampoline(Value *closure);
Value *tailcall_apply_closure(Value *_clos, Value *arg);
