#ifndef __MEMORY_MANAGEMENT_H__
#define __MEMORY_MANAGEMENT_H__
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
Value_Int8 *makeInt8(int8_t i);
Value_Int16 *makeInt16(int16_t i);
Value_Int32 *makeInt32(int32_t i);
Value_Int64 *makeInt64(int64_t i);
Value_String *makeEmptyString(size_t l);
Value_String *makeString(char *);

Value_Pointer *makePointer(void *);
Value_Array *makeArray(int length);
Value_World *makeWorld(void);

#endif
