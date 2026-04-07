#include "stringOps.h"
#include "refc_util.h"

Idris2_Value *tail(Idris2_Value *input) {
  Idris2_String *tailStr = IDRIS2_NEW_VALUE(Idris2_String);
  tailStr->header.tag = STRING_TAG;
  Idris2_String *s = (Idris2_String *)input;
  int l = strlen(s->str);
  if (l == 0)
    return (Idris2_Value *)&idris2_predefined_nullstring;

  tailStr->str = malloc(l);
  IDRIS2_REFC_VERIFY(tailStr->str, "malloc failed");
  memset(tailStr->str, 0, l);
  memcpy(tailStr->str, s->str + 1, l - 1);
  return (Idris2_Value *)tailStr;
}

Idris2_Value *reverse(Idris2_Value *str) {
  Idris2_String *retVal = IDRIS2_NEW_VALUE(Idris2_String);
  retVal->header.tag = STRING_TAG;
  Idris2_String *input = (Idris2_String *)str;
  int l = strlen(input->str);
  retVal->str = malloc(l + 1);
  IDRIS2_REFC_VERIFY(retVal->str, "malloc failed");
  memset(retVal->str, 0, l + 1);
  char *p = retVal->str;
  char *q = input->str + (l - 1);
  for (int i = 0; i < l; i++) {
    *p++ = *q--;
  }
  return (Idris2_Value *)retVal;
}

Idris2_Value *strIndex(Idris2_Value *str, Idris2_Value *i) {
  char *s = ((Idris2_String *)str)->str;
  int idx = idris2_vp_to_Int64(i);
  return (Idris2_Value *)idris2_mkChar(s[idx]);
}

Idris2_Value *strCons(Idris2_Value *c, Idris2_Value *str) {
  int l = strlen(((Idris2_String *)str)->str);
  Idris2_String *retVal = idris2_mkEmptyString(l + 2);
  retVal->str[0] = idris2_vp_to_Char(c);
  memcpy(retVal->str + 1, ((Idris2_String *)str)->str, l);
  return (Idris2_Value *)retVal;
}

Idris2_Value *strAppend(Idris2_Value *a, Idris2_Value *b) {
  int la = strlen(((Idris2_String *)a)->str);
  int lb = strlen(((Idris2_String *)b)->str);
  Idris2_String *retVal = idris2_mkEmptyString(la + lb + 1);
  memcpy(retVal->str, ((Idris2_String *)a)->str, la);
  memcpy(retVal->str + la, ((Idris2_String *)b)->str, lb);
  return (Idris2_Value *)retVal;
}

Idris2_Value *strSubstr(Idris2_Value *start, Idris2_Value *len,
                        Idris2_Value *s) {
  char *input = ((Idris2_String *)s)->str;
  int offset = idris2_vp_to_Int64(start); /* start and len was come from Nat. */
  int l = idris2_vp_to_Int64(len);

  int tailLen = strlen(input) - offset;
  if (tailLen < l) {
    l = tailLen;
  }

  Idris2_String *retVal = idris2_mkEmptyString(l + 1);
  memcpy(retVal->str, input + offset, l);

  return (Idris2_Value *)retVal;
}

char *fastPack(Idris2_Value *charList) {
  Idris2_Constructor *current;

  int l = 0;
  current = (Idris2_Constructor *)charList;
  while (current != NULL) {
    l++;
    current = (Idris2_Constructor *)current->args[1];
  }

  char *retVal = malloc(l + 1);
  retVal[l] = 0;

  int i = 0;
  current = (Idris2_Constructor *)charList;
  while (current != NULL) {
    retVal[i++] = idris2_vp_to_Char(current->args[0]);
    current = (Idris2_Constructor *)current->args[1];
  }

  return retVal;
}

Idris2_Value *fastUnpack(char *str) {
  if (str[0] == '\0') {
    return NULL;
  }

  Idris2_Constructor *retVal = idris2_newConstructor(2, 1);
  retVal->args[0] = idris2_mkChar(str[0]);

  int i = 1;
  Idris2_Constructor *current = (Idris2_Constructor *)retVal;
  Idris2_Constructor *next;
  while (str[i] != '\0') {
    next = idris2_newConstructor(2, 1);
    next->args[0] = idris2_mkChar(str[i]);
    current->args[1] = (Idris2_Value *)next;

    i++;
    current = next;
  }
  current->args[1] = NULL;

  return (Idris2_Value *)retVal;
}

char *fastConcat(Idris2_Value *strList) {
  Idris2_Constructor *current;

  int totalLength = 0;
  current = (Idris2_Constructor *)strList;
  while (current != NULL) {
    totalLength += strlen(((Idris2_String *)current->args[0])->str);
    current = (Idris2_Constructor *)current->args[1];
  }

  char *retVal = malloc(totalLength + 1);
  retVal[totalLength] = '\0';

  char *currentStr;
  int currentStrLen;
  int offset = 0;
  current = (Idris2_Constructor *)strList;
  while (current != NULL) {
    currentStr = ((Idris2_String *)current->args[0])->str;
    currentStrLen = strlen(currentStr);
    memcpy(retVal + offset, currentStr, currentStrLen);

    offset += currentStrLen;
    current = (Idris2_Constructor *)current->args[1];
  }

  return retVal;
}

typedef struct {
  char *str;
  int pos;
} String_Iterator;

Idris2_Value *stringIteratorNew(char *str) {
  int l = strlen(str);

  String_Iterator *it = (String_Iterator *)malloc(sizeof(String_Iterator));
  IDRIS2_REFC_VERIFY(it, "malloc failed");
  it->str = (char *)malloc(l + 1);
  it->pos = 0;
  memcpy(it->str, str, l + 1); // Take a copy of str, in case it gets GCed

  return (Idris2_Value *)idris2_makeGCPointer(
      it, (Idris2_Closure *)idris2_mkClosure(
              (Idris2_Value * (*)()) onCollectStringIterator, 2, 0));
}

Idris2_Value *onCollectStringIterator(Idris2_Pointer *ptr, void *null) {
  String_Iterator *it = (String_Iterator *)ptr->p;
  free(it->str);
  free(it);
  return NULL;
}

Idris2_Value *stringIteratorToString(void *a, char *str, Idris2_Value *it_p,
                                     Idris2_Closure *f) {
  String_Iterator *it = ((Idris2_GCPointer *)it_p)->p->p;
  Idris2_Value *strVal = (Idris2_Value *)idris2_mkString(it->str + it->pos);
  return idris2_apply_closure(idris2_newReference((Idris2_Value *)f), strVal);
}

// contrib/Data.String.Iterator.uncons :
//   (str : String) -> (1 it : StringIterator str) -> UnconsResult str
Idris2_Value *stringIteratorNext(char *s, Idris2_Value *it_p) {
  String_Iterator *it = (String_Iterator *)((Idris2_GCPointer *)it_p)->p->p;
  char c = it->str[it->pos];

  if (c == '\0')
    return NULL; // EOF [nil]

  it->pos++; // Ok to do this as StringIterator linear

  // Character [cons]
  Idris2_Constructor *retVal =
      (Idris2_Constructor *)idris2_newConstructor(2, 1);
  retVal->args[0] = idris2_mkChar(c);
  retVal->args[1] = idris2_newReference(it_p);

  return (Idris2_Value *)retVal;
}
