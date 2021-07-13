#pragma once

#include "cBackend.h"

Value *newValue(void);
Value *newReference(Value *source);
void removeReference(Value *source);

Value_Arglist *newArglist(int missing, int total);
Value_Constructor *newConstructor(int total, int tag, const char *name);

// copies arglist, no pointer bending
Value_Closure *makeClosureFromArglist(fun_ptr_t f, Value_Arglist *);

Value_Double *makeDouble(double d);
Value_Char *makeChar(char d);
Value_Bits8 *makeBits8(uint8_t i);
Value_Bits16 *makeBits16(uint16_t i);
Value_Bits32 *makeBits32(uint32_t i);
Value_Bits64 *makeBits64(uint64_t i);
Value_Int8 *makeInt8(int8_t i);
Value_Int16 *makeInt16(int16_t i);
Value_Int32 *makeInt32(int32_t i);
Value_Int64 *makeInt64(int64_t i);
Value_Int8 *makeBool(int p);
Value_Integer *makeInteger();
Value_Integer *makeIntegerLiteral(char *i);
Value_String *makeString(const char *);
Value_String *makeStringWithLength(const char *, size_t);
Value_String *makeStringConcat(const char *a, size_t a_len, const char *b, size_t b_len);
Value_String *makeStringPrintf(const char* fmt, ...)
#if defined(__clang__) || defined(__GNUC__)
__attribute__ ((format(printf, 1, 2)))
#endif
;

Value_Pointer *makePointer(void *);
Value_GCPointer *makeGCPointer(void *ptr_Raw, Value_Closure *onCollectFct);
Value_Buffer *makeBuffer(void *buf);
Value_Array *makeArray(int length);
Value_World *makeWorld(void);
