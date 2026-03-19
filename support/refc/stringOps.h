#pragma once

#include "cBackend.h"
#include "casts.h"
#include "utf8.h"

/* stringLength returns the number of Unicode code points, not bytes. */
#define stringLength(x) \
  (idris2_mkInt64((int64_t)utf8_cp_count(((Value_String *)(x))->str)))
#define head(x) (idris2_cast_String_to_Char(x))
Value *tail(Value *str);
Value *reverse(Value *str);
Value *strIndex(Value *str, Value *i);
Value *strCons(Value *c, Value *str);
Value *strAppend(Value *a, Value *b);
Value *strSubstr(Value *s, Value *start, Value *len);
char *fastPack(Value *charList);
Value *fastUnpack(char *str);
char *fastConcat(Value *strList);

Value *stringIteratorNew(char *str);
Value *onCollectStringIterator(Value_Pointer *ptr, void *null);
Value *stringIteratorToString(void *a, char *str, Value *it_p,
                              Value_Closure *f);
Value *stringIteratorNext(char *s, Value *it_p);
