#pragma once

#include "cBackend.h"
#include "casts.h"

/* stringLength : String -> Int64!? WTH!. do you have over 4Gbytes text on
 * memory!? */
#define stringLength(x) (idris2_mkInt64(strlen(((Idris2_String *)(x))->str)))
#define head(x) (idris2_cast_String_to_Char(x))
Idris2_Value *tail(Idris2_Value *str);
Idris2_Value *reverse(Idris2_Value *str);
Idris2_Value *strIndex(Idris2_Value *str, Idris2_Value *i);
Idris2_Value *strCons(Idris2_Value *c, Idris2_Value *str);
Idris2_Value *strAppend(Idris2_Value *a, Idris2_Value *b);
Idris2_Value *strSubstr(Idris2_Value *s, Idris2_Value *start,
                        Idris2_Value *len);
char *fastPack(Idris2_Value *charList);
Idris2_Value *fastUnpack(char *str);
char *fastConcat(Idris2_Value *strList);

Idris2_Value *stringIteratorNew(char *str);
Idris2_Value *onCollectStringIterator(Idris2_Pointer *ptr, void *null);
Idris2_Value *stringIteratorToString(void *a, char *str, Idris2_Value *it_p,
                                     Idris2_Closure *f);
Idris2_Value *stringIteratorNext(char *s, Idris2_Value *it_p);
