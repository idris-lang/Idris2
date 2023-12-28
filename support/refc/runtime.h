#pragma once

#include "cBackend.h"

void missing_ffi();

Value *apply_closure(Value *, Value *arg);

int extractInt(Value *);
Value *trampoline(Value *closure);
Value *tailcall_apply_closure(Value *_clos, Value *arg);
