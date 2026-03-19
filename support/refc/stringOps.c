#include "stringOps.h"
#include "refc_util.h"
#include "utf8.h"

Value *tail(Value *input) {
  Value_String *s = (Value_String *)input;
  if (s->str[0] == '\0')
    return (Value *)&idris2_predefined_nullstring;

  int skip = utf8_seq_len(s->str);
  int rest = strlen(s->str + skip);

  if (rest == 0)
    return (Value *)&idris2_predefined_nullstring;

  Value_String *retVal = idris2_mkEmptyString(rest + 1);
  memcpy(retVal->str, s->str + skip, rest);
  return (Value *)retVal;
}

Value *reverse(Value *str) {
  Value_String *input = (Value_String *)str;
  const char *s = input->str;
  int byteLen = strlen(s);

  if (byteLen == 0)
    return (Value *)&idris2_predefined_nullstring;

  /* Collect code points */
  size_t cpCount = utf8_cp_count(s);
  uint32_t *cps = malloc(cpCount * sizeof(uint32_t));
  int *widths = malloc(cpCount * sizeof(int));
  IDRIS2_REFC_VERIFY(cps, "malloc failed");
  IDRIS2_REFC_VERIFY(widths, "malloc failed");

  const char *p = s;
  for (size_t i = 0; i < cpCount; i++) {
    widths[i] = utf8_decode(p, &cps[i]);
    p += widths[i];
  }

  /* Re-encode in reverse order */
  Value_String *retVal = idris2_mkEmptyString(byteLen + 1);
  char *out = retVal->str;
  for (size_t i = cpCount; i > 0; i--) {
    out += utf8_encode(cps[i - 1], out);
  }
  *out = '\0';

  free(cps);
  free(widths);
  return (Value *)retVal;
}

Value *strIndex(Value *str, Value *i) {
  const char *s = ((Value_String *)str)->str;
  size_t idx = (size_t)idris2_vp_to_Int64(i);
  size_t byteOff = utf8_cp_to_byte_offset(s, idx);
  uint32_t cp;
  utf8_decode(s + byteOff, &cp);
  return (Value *)idris2_mkChar(cp);
}

Value *strCons(Value *c, Value *str) {
  uint32_t cp = idris2_vp_to_Char(c);
  const char *rest = ((Value_String *)str)->str;
  int restLen = strlen(rest);

  char cpBuf[4];
  int cpLen = utf8_encode(cp, cpBuf);

  Value_String *retVal = idris2_mkEmptyString(cpLen + restLen + 1);
  memcpy(retVal->str, cpBuf, cpLen);
  memcpy(retVal->str + cpLen, rest, restLen);
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
  const char *input = ((Value_String *)s)->str;
  size_t offset = (size_t)idris2_vp_to_Int64(start);
  size_t cpLen  = (size_t)idris2_vp_to_Int64(len);

  size_t byteStart = utf8_cp_to_byte_offset(input, offset);
  size_t byteEnd   = utf8_cp_to_byte_offset(input + byteStart, cpLen);

  if (byteEnd == 0)
    return (Value *)&idris2_predefined_nullstring;

  Value_String *retVal = idris2_mkEmptyString(byteEnd + 1);
  memcpy(retVal->str, input + byteStart, byteEnd);
  return (Value *)retVal;
}

char *fastPack(Value *charList) {
  /* First pass: compute total byte length */
  size_t totalBytes = 0;
  Value_Constructor *cur = (Value_Constructor *)charList;
  while (cur != NULL) {
    uint32_t cp = idris2_vp_to_Char(cur->args[0]);
    char buf[4];
    totalBytes += utf8_encode(cp, buf);
    cur = (Value_Constructor *)cur->args[1];
  }

  char *retVal = malloc(totalBytes + 1);
  retVal[totalBytes] = '\0';

  char *p = retVal;
  cur = (Value_Constructor *)charList;
  while (cur != NULL) {
    uint32_t cp = idris2_vp_to_Char(cur->args[0]);
    p += utf8_encode(cp, p);
    cur = (Value_Constructor *)cur->args[1];
  }

  return retVal;
}

Value *fastUnpack(char *str) {
  if (str[0] == '\0')
    return NULL;

  uint32_t cp;
  int w = utf8_decode(str, &cp);

  Value_Constructor *retVal = idris2_newConstructor(2, 1);
  retVal->args[0] = idris2_mkChar(cp);

  Value_Constructor *current = retVal;
  const char *p = str + w;
  while (*p != '\0') {
    w = utf8_decode(p, &cp);
    Value_Constructor *next = idris2_newConstructor(2, 1);
    next->args[0] = idris2_mkChar(cp);
    current->args[1] = (Value *)next;
    current = next;
    p += w;
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

  /* onCollectStringIterator has a concrete signature but is stored as ClosureFun
   * for later dispatch — suppress the cast-function-type warning intentionally. */
#if defined(__clang__)
#  pragma clang diagnostic push
#  pragma clang diagnostic ignored "-Wcast-function-type-mismatch"
#elif defined(__GNUC__)
#  pragma GCC diagnostic push
#  pragma GCC diagnostic ignored "-Wcast-function-type"
#endif
  return (Value *)idris2_makeGCPointer(
      it, (Value_Closure *)idris2_mkClosure(
              (ClosureFun) onCollectStringIterator, 2, 0));
#if defined(__clang__)
#  pragma clang diagnostic pop
#elif defined(__GNUC__)
#  pragma GCC diagnostic pop
#endif
}

Value *onCollectStringIterator(Value_Pointer *ptr, void *IDRIS2_UNUSED null) {
  String_Iterator *it = (String_Iterator *)ptr->p;
  free(it->str);
  free(it);
  return NULL;
}

Value *stringIteratorToString(void *IDRIS2_UNUSED a, char *IDRIS2_UNUSED str,
                              Value *it_p, Value_Closure *f) {
  String_Iterator *it = ((Value_GCPointer *)it_p)->p->p;
  Value *strVal = (Value *)idris2_mkString(it->str + it->pos);
  return idris2_apply_closure(idris2_newReference((Value *)f), strVal);
}

// contrib/Data.String.Iterator.uncons :
//   (str : String) -> (1 it : StringIterator str) -> UnconsResult str
Value *stringIteratorNext(char *IDRIS2_UNUSED s, Value *it_p) {
  String_Iterator *it = (String_Iterator *)((Value_GCPointer *)it_p)->p->p;
  char *p = it->str + it->pos;

  if (*p == '\0')
    return NULL; // EOF [nil]

  uint32_t cp;
  int w = utf8_decode(p, &cp);
  it->pos += w; // advance by full code-point width (StringIterator is linear)

  // Character [cons]
  Value_Constructor *retVal = (Value_Constructor *)idris2_newConstructor(2, 1);
  retVal->args[0] = idris2_mkChar(cp);
  retVal->args[1] = idris2_newReference(it_p);

  return (Value *)retVal;
}
