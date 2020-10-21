#ifndef __STRING_OPS_H__
#define __STRING_OPS_H__

#include "cBackend.h"

Value *stringLength(Value *);
Value *head(Value *str);
Value *tail(Value *str);
Value *reverse(Value *str);
Value *strIndex(Value *str, Value *i);
Value *strCons(Value *c, Value *str);
Value *strAppend(Value *a, Value *b);
Value *strSubstr(Value *s, Value *start, Value *len);

#endif
