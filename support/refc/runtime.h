#ifndef __RUNTIME_H__
#define __RUNTIME_H__

#include "cBackend.h"

Value *apply_closure(Value *, Value *arg);
void push_Arglist(Value_Arglist *arglist, Value *arg);

int extractInt(Value *);
Value *trampoline(Value *closure);
Value *tailcall_apply_closure(Value *_clos, Value *arg);
#endif
