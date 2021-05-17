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

Value *tail(Value *input)
{
    Value_String *tailStr = (Value_String *)newValue();
    tailStr->header.tag = STRING_TAG;
    Value_String *s = (Value_String *)input;
    int l = strlen(s->str);
    if(l != 0)
    {
        tailStr->str = malloc(l);
        memset(tailStr->str, 0, l);
        memcpy(tailStr->str, s->str + 1, l - 1);
        return (Value *)tailStr;
    }
    else
    {
        tailStr->str = malloc(1);
        tailStr->str[0] = '\0';
        return (Value *)tailStr;
    }
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
    for (int i = 0; i < l; i++)
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

Value *strSubstr(Value *start, Value *len, Value *s)
{
    char *input = ((Value_String *)s)->str;
    int offset = extractInt(start);
    int l = extractInt(len);

    int tailLen = strlen(input);
    if (tailLen < l)
    {
        l = tailLen;
    }

    Value_String *retVal = makeEmptyString(l + 1);
    memcpy(retVal->str, input + offset, l);

    return (Value *)retVal;
}

char *fastPack(Value *charList)
{
    Value_Constructor *current;

    int l = 0;
    current = (Value_Constructor *)charList;
    while (current->total == 2)
    {
        l ++;
        current = (Value_Constructor *)current->args[1];
    }

    char *retVal = malloc(l + 1);
    retVal[l] = 0;

    int i = 0;
    current = (Value_Constructor *)charList;
    while (current->total == 2)
    {
        retVal[i++] = ((Value_Char *)current->args[0])->c;
        current = (Value_Constructor *)current->args[1];
    }

    return retVal;
}

Value *fastUnpack(char *str)
{
    if (str[0] == '\0') {
        return (Value *)newConstructor(0, 0, "Prelude_Types_Nil");
    }

    Value_Constructor *retVal = newConstructor(2, 1, "Prelude_Types__colon_colon");
    retVal->args[0] = (Value *)makeChar(str[0]);

    int i = 1;
    Value_Constructor *current = retVal;
    Value_Constructor *next;
    while (str[i] != '\0') {
        next = newConstructor(2, 1, "Prelude_Types__colon_colon");
        next->args[0] = (Value *)makeChar(str[i]);
        current->args[1] = (Value *)next;

        i ++;
        current = next;
    }
    current->args[1] = (Value *)newConstructor(0, 0, "Prelude_Types_Nil");

    return (Value *)retVal;
}

char *fastConcat(Value *strList)
{
    Value_Constructor *current;

    int totalLength = 0;
    current = (Value_Constructor *)strList;
    while (current->total == 2)
    {
        totalLength += strlen(((Value_String *)current->args[0])->str);
        current = (Value_Constructor *)current->args[1];
    }

    char *retVal = malloc(totalLength + 1);
    retVal[totalLength + 1] = '\0';

    char *currentStr;
    int currentStrLen;
    int offset = 0;
    current = (Value_Constructor *)strList;
    while (current->total == 2)
    {
        currentStr = ((Value_String *)current->args[0])->str;
        currentStrLen = strlen(currentStr);
        memcpy(retVal + offset, currentStr, currentStrLen);

        offset += currentStrLen;
        current = (Value_Constructor *)current->args[1];
    }

    return retVal;
}
