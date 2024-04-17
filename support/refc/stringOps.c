#include "stringOps.h"
#include "refc_util.h"

Value *tail(Value *input) {
  Value_String *tailStr = IDRIS2_NEW_VALUE(Value_String);
  tailStr->header.tag = STRING_TAG;
  Value_String *s = (Value_String *)input;
  int l = strlen(s->str);
  if (l != 0) {
    tailStr->str = malloc(l);
    IDRIS2_REFC_VERIFY(tailStr->str, "malloc failed");
    memset(tailStr->str, 0, l);
    memcpy(tailStr->str, s->str + 1, l - 1);
    return (Value *)tailStr;
  } else {
    tailStr->str = malloc(1);
    IDRIS2_REFC_VERIFY(tailStr->str, "malloc failed");
    tailStr->str[0] = '\0';
    return (Value *)tailStr;
  }
}

Value *reverse(Value *str) {
  Value_String *retVal = IDRIS2_NEW_VALUE(Value_String);
  retVal->header.tag = STRING_TAG;
  Value_String *input = (Value_String *)str;
  int l = strlen(input->str);
  retVal->str = malloc(l + 1);
  IDRIS2_REFC_VERIFY(retVal->str, "malloc failed");
  memset(retVal->str, 0, l + 1);
  char *p = retVal->str;
  char *q = input->str + (l - 1);
  for (int i = 0; i < l; i++) {
    *p++ = *q--;
  }
  return (Value *)retVal;
}

Value *strIndex(Value *str, Value *i) {
  char *s = ((Value_String *)str)->str;
  int idx = idris2_vp_to_Int64(i);
  return (Value *)idris2_mkChar(s[idx]);
}

Value *strCons(Value *c, Value *str) {
  int l = strlen(((Value_String *)str)->str);
  Value_String *retVal = idris2_mkEmptyString(l + 2);
  retVal->str[0] = idris2_vp_to_Char(c);
  memcpy(retVal->str + 1, ((Value_String *)str)->str, l);
  return (Value *)retVal;
}

Value *strAppend(Value *a, Value *b) {
  int la = strlen(((Value_String *)a)->str);
  int lb = strlen(((Value_String *)b)->str);
  Value_String *retVal = idris2_mkEmptyString(la + lb + 1);
  memcpy(retVal->str, ((Value_String *)a)->str, la);
  memcpy(retVal->str + la, ((Value_String *)b)->str, lb);
  return (Value *)retVal;
}

Value *strSubstr(Value *start, Value *len, Value *s) {
  char *input = ((Value_String *)s)->str;
  int offset = idris2_vp_to_Int64(start); /* start and len was come from Nat. */
  int l = idris2_vp_to_Int64(len);

  int tailLen = strlen(input) - offset;
  if (tailLen < l) {
    l = tailLen;
  }

  Value_String *retVal = idris2_mkEmptyString(l + 1);
  memcpy(retVal->str, input + offset, l);

  return (Value *)retVal;
}

char *fastPack(Value *charList) {
  Value_Constructor *current;

  int l = 0;
  current = (Value_Constructor *)charList;
  while (current != NULL) {
    l++;
    current = (Value_Constructor *)current->args[1];
  }

  char *retVal = malloc(l + 1);
  retVal[l] = 0;

  int i = 0;
  current = (Value_Constructor *)charList;
  while (current != NULL) {
    retVal[i++] = idris2_vp_to_Char(current->args[0]);
    current = (Value_Constructor *)current->args[1];
  }

  return retVal;
}

Value *fastUnpack(char *str) {
  if (str[0] == '\0') {
    return NULL;
  }

  Value_Constructor *retVal = idris2_newConstructor(2, 1);
  retVal->args[0] = idris2_mkChar(str[0]);

  int i = 1;
  Value_Constructor *current = (Value_Constructor *)retVal;
  Value_Constructor *next;
  while (str[i] != '\0') {
    next = idris2_newConstructor(2, 1);
    next->args[0] = idris2_mkChar(str[i]);
    current->args[1] = (Value *)next;

    i++;
    current = next;
  }
  current->args[1] = NULL;

  return (Value *)retVal;
}

char *fastConcat(Value *strList) {
  Value_Constructor *current;

  int totalLength = 0;
  current = (Value_Constructor *)strList;
  while (current != NULL) {
    totalLength += strlen(((Value_String *)current->args[0])->str);
    current = (Value_Constructor *)current->args[1];
  }

  char *retVal = malloc(totalLength + 1);
  retVal[totalLength] = '\0';

  char *currentStr;
  int currentStrLen;
  int offset = 0;
  current = (Value_Constructor *)strList;
  while (current != NULL) {
    currentStr = ((Value_String *)current->args[0])->str;
    currentStrLen = strlen(currentStr);
    memcpy(retVal + offset, currentStr, currentStrLen);

    offset += currentStrLen;
    current = (Value_Constructor *)current->args[1];
  }

  return retVal;
}

typedef struct {
  char *str;
  int pos;
} String_Iterator;

Value *stringIteratorNew(char *str) {
  int l = strlen(str);

  String_Iterator *it = (String_Iterator *)malloc(sizeof(String_Iterator));
  IDRIS2_REFC_VERIFY(it, "malloc failed");
  it->str = (char *)malloc(l + 1);
  it->pos = 0;
  memcpy(it->str, str, l + 1); // Take a copy of str, in case it gets GCed

  return (Value *)idris2_makeGCPointer(
      it, (Value_Closure *)idris2_mkClosure(
              (Value * (*)()) onCollectStringIterator, 2, 0));
}

Value *onCollectStringIterator(Value_Pointer *ptr, void *null) {
  String_Iterator *it = (String_Iterator *)ptr->p;
  free(it->str);
  free(it);
  return NULL;
}

Value *stringIteratorToString(void *a, char *str, Value *it_p,
                              Value_Closure *f) {
  String_Iterator *it = ((Value_GCPointer *)it_p)->p->p;
  Value *strVal = (Value *)idris2_mkString(it->str + it->pos);
  return idris2_apply_closure(idris2_newReference((Value *)f), strVal);
}

// contrib/Data.String.Iterator.uncons :
//   (str : String) -> (1 it : StringIterator str) -> UnconsResult str
Value *stringIteratorNext(char *s, Value *it_p) {
  String_Iterator *it = (String_Iterator *)((Value_GCPointer *)it_p)->p->p;
  char c = it->str[it->pos];

  if (c == '\0')
    return NULL; // EOF [nil]

  it->pos++; // Ok to do this as StringIterator linear

  // Character [cons]
  Value_Constructor *retVal = (Value_Constructor *)idris2_newConstructor(2, 1);
  retVal->args[0] = idris2_mkChar(c);
  retVal->args[1] = idris2_newReference(it_p);

  return (Value *)retVal;
}
