#include "stringOps.h"

Value *stringLength(Value *s)
{
    int length = strlen(((Value_String *)s)->str);
    return (Value *)makeInt32(length);
}

Value *head(Value *str)
{
    Value_Char *c = (Value_Char *)newValue();
    c->header.tag = CHAR_TAG;
    c->c = ((Value_String *)str)->str[0];
    return (Value *)c;
}

Value *tail(Value *str)
{
    Value_Char *c = (Value_Char *)newValue();
    c->header.tag = CHAR_TAG;
    Value_String *s = (Value_String *)str;
    int l = strlen(s->str);
    c->c = s->str[l - 1];
    return (Value *)c;
}

Value *reverse(Value *str)
{
    Value_String *retVal = (Value_String *)newValue();
    retVal->header.tag = STRING_TAG;
    Value_String *input = (Value_String *)str;
    int l = strlen(input->str);
    retVal->str = malloc(l + 1);
    memset(retVal->str, 0, l + 1);
    char *p = retVal->str;
    char *q = input->str + (l - 1);
    for (int i = 1; i < l; i++)
    {
        *p++ = *q--;
    }
    return (Value *)retVal;
}

Value *strIndex(Value *str, Value *i)
{
    Value_Char *c;
    switch (i->header.tag)
    {
    case INT64_TAG:
        c = makeChar(((Value_String *)str)->str[((Value_Int64 *)i)->i64]);
        return (Value *)c;
    default:
        c = makeChar(((Value_String *)str)->str[((Value_Int32 *)i)->i32]);
        return (Value *)c;
    }
}

Value *strCons(Value *c, Value *str)
{
    int l = strlen(((Value_String *)str)->str);
    Value_String *retVal = makeEmptyString(l + 2);
    retVal->str[0] = ((Value_Char *)c)->c;
    memcpy(retVal->str + 1, ((Value_String *)str)->str, l);
    return (Value *)retVal;
}

Value *strAppend(Value *a, Value *b)
{
    int la = strlen(((Value_String *)a)->str);
    int lb = strlen(((Value_String *)b)->str);
    Value_String *retVal = makeEmptyString(la + lb + 1);
    memcpy(retVal->str, ((Value_String *)a)->str, la);
    memcpy(retVal->str + la, ((Value_String *)b)->str, lb);
    return (Value *)retVal;
}

Value *strSubstr(Value *s, Value *start, Value *len)
{
    Value_String *retVal;
    switch (len->header.tag)
    {
    case INT64_TAG:
        retVal = makeEmptyString(((Value_Int64 *)len)->i64 + 1);
        memcpy(retVal->str, ((Value_String *)s)->str, ((Value_Int64 *)len)->i64);
        return (Value *)retVal;
    default:
        retVal = makeEmptyString(((Value_Int32 *)len)->i32 + 1);
        memcpy(retVal->str, ((Value_String *)s)->str, ((Value_Int32 *)len)->i32);
        return (Value *)retVal;
    }
}
