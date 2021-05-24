#include "mathFunctions.h"
#include "runtime.h"
#include "memoryManagement.h"

double unpackDouble(Value *d)
{
    return ((Value_Double *)d)->d;
}

/* add */
Value *add_Int(Value *x, Value *y)
{
    return (Value *)makeInt(((Value_Int *)x)->i64 + ((Value_Int *)y)->i64);
}
Value *add_double(Value *x, Value *y)
{
    return (Value *)makeDouble(((Value_Double *)x)->d + ((Value_Double *)y)->d);
}

/* sub */
Value *sub_Int(Value *x, Value *y)
{
    return (Value *)makeInt(((Value_Int *)x)->i64 - ((Value_Int *)y)->i64);
}
Value *sub_double(Value *x, Value *y)
{
    return (Value *)makeDouble(((Value_Double *)x)->d - ((Value_Double *)y)->d);
}

/* negate */
Value *negate_Int(Value *x)
{
    return (Value *)makeInt(-((Value_Int *)x)->i64);
}
Value *negate_double(Value *x)
{
    return (Value *)makeDouble(-((Value_Double *)x)->d);
}
/* mul */
Value *mul_Int(Value *x, Value *y)
{
    return (Value *)makeInt(((Value_Int *)x)->i64 * ((Value_Int *)y)->i64);
}
Value *mul_double(Value *x, Value *y)
{
    return (Value *)makeDouble(((Value_Double *)x)->d * ((Value_Double *)y)->d);
}

/* div */
Value *div_Int(Value *x, Value *y)
{
    return (Value *)makeInt(((Value_Int *)x)->i64 / ((Value_Int *)y)->i64);
}
Value *div_double(Value *x, Value *y)
{
    return (Value *)makeDouble(((Value_Double *)x)->d / ((Value_Double *)y)->d);
}

/* mod */
Value *mod_Int(Value *x, Value *y)
{
    return (Value *)makeInt(((Value_Int *)x)->i64 % ((Value_Int *)y)->i64);
}

/* shiftl */
Value *shiftl_Int(Value *x, Value *y)
{
    return (Value *)makeInt(((Value_Int *)x)->i64 << ((Value_Int *)y)->i64);
}

/* shiftr */
Value *shiftr_Int(Value *x, Value *y)
{
    return (Value *)makeInt(((Value_Int *)x)->i64 >> ((Value_Int *)y)->i64);
}

/* and */
Value *and_Int(Value *x, Value *y)
{
    return (Value *)makeInt(((Value_Int *)x)->i64 & ((Value_Int *)y)->i64);
}

/* or */
Value *or_Int(Value *x, Value *y)
{
    return (Value *)makeInt(((Value_Int *)x)->i64 | ((Value_Int *)y)->i64);
}

/* xor */
Value *xor_Int(Value *x, Value *y)
{
    return (Value *)makeInt(((Value_Int *)x)->i64 ^ ((Value_Int *)y)->i64);
}

/* lt */
Value *lt_Int(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int *)x)->i64 < ((Value_Int *)y)->i64);
}
Value *lt_double(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Double *)x)->d < ((Value_Double *)y)->d);
}
Value *lt_char(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Char *)x)->c < ((Value_Char *)y)->c);
}

Value *lt_string(Value *x, Value *y)
{
    return (Value *)makeBool(strcmp(((Value_String *)x)->str, ((Value_String *)y)->str) < 0);
}

/* gt */
Value *gt_Int(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int *)x)->i64 > ((Value_Int *)y)->i64);
}
Value *gt_double(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Double *)x)->d > ((Value_Double *)y)->d);
}
Value *gt_char(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Char *)x)->c > ((Value_Char *)y)->c);
}

Value *gt_string(Value *x, Value *y)
{
    return (Value *)makeBool(strcmp(((Value_String *)x)->str, ((Value_String *)y)->str) > 0);
}

/* eq */
Value *eq_Int(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int *)x)->i64 == ((Value_Int *)y)->i64);
}
Value *eq_double(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Double *)x)->d == ((Value_Double *)y)->d);
}
Value *eq_char(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Char *)x)->c == ((Value_Char *)y)->c);
}
Value *eq_string(Value *x, Value *y)
{
    return (Value *)makeBool(!strcmp(((Value_String *)x)->str, ((Value_String *)y)->str));
}

/* lte */
Value *lte_Int(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int *)x)->i64 <= ((Value_Int *)y)->i64);
}
Value *lte_double(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Double *)x)->d <= ((Value_Double *)y)->d);
}
Value *lte_char(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Char *)x)->c <= ((Value_Char *)y)->c);
}

Value *lte_string(Value *x, Value *y)
{
    return (Value *)makeBool(strcmp(((Value_String *)x)->str, ((Value_String *)y)->str) <= 0);
}

/* gte */
Value *gte_Int(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int *)x)->i64 >= ((Value_Int *)y)->i64);
}

Value *gte_double(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Double *)x)->d >= ((Value_Double *)y)->d);
}

Value *gte_char(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Char *)x)->c >= ((Value_Char *)y)->c);
}

Value *gte_string(Value *x, Value *y)
{
    return (Value *)makeBool(strcmp(((Value_String *)x)->str, ((Value_String *)y)->str) >= 0);
}
