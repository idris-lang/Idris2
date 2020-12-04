#include "mathFunctions.h"
#include "runtime.h"
#include "memoryManagement.h"

double unpackDouble(Value *d)
{
    return ((Value_Double *)d)->d;
}

Value *believe_me(Value *a, Value *b, Value *c)
{
    return c;
}

/* add */
Value *add_i32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 + ((Value_Int32 *)y)->i32);
}
Value *add_i64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 + ((Value_Int64 *)y)->i64);
}
Value *add_double(Value *x, Value *y)
{
    return (Value *)makeDouble(((Value_Double *)x)->d + ((Value_Double *)y)->d);
}

/* sub */
Value *sub_i32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 - ((Value_Int32 *)y)->i32);
}
Value *sub_i64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 - ((Value_Int64 *)y)->i64);
}
Value *sub_double(Value *x, Value *y)
{
    return (Value *)makeDouble(((Value_Double *)x)->d - ((Value_Double *)y)->d);
}

/* mul */
Value *mul_i32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 * ((Value_Int32 *)y)->i32);
}
Value *mul_i64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 * ((Value_Int64 *)y)->i64);
}
Value *mul_double(Value *x, Value *y)
{
    return (Value *)makeDouble(((Value_Double *)x)->d * ((Value_Double *)y)->d);
}

/* div */
Value *div_i32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 / ((Value_Int32 *)y)->i32);
}
Value *div_i64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 / ((Value_Int64 *)y)->i64);
}
Value *div_double(Value *x, Value *y)
{
    return (Value *)makeDouble(((Value_Double *)x)->d / ((Value_Double *)y)->d);
}

/* mod */
Value *mod_i32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 % ((Value_Int32 *)y)->i32);
}
Value *mod_i64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 % ((Value_Int64 *)y)->i64);
}

/* shiftl */
Value *shiftl_i32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 << ((Value_Int32 *)y)->i32);
}
Value *shiftl_i64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 << ((Value_Int64 *)y)->i64);
}

/* shiftr */
Value *shiftr_i32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 >> ((Value_Int32 *)y)->i32);
}
Value *shiftr_i64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 >> ((Value_Int64 *)y)->i64);
}

/* and */
Value *and_i32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 & ((Value_Int32 *)y)->i32);
}
Value *and_i64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 & ((Value_Int64 *)y)->i64);
}

/* or */
Value *or_i32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 | ((Value_Int32 *)y)->i32);
}
Value *or_i64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 | ((Value_Int64 *)y)->i64);
}

/* xor */
Value *xor_i32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 ^ ((Value_Int32 *)y)->i32);
}
Value *xor_i64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 ^ ((Value_Int64 *)y)->i64);
}

/* lt */
Value *lt_i32(Value *x, Value *y)
{
    if (((Value_Int32 *)x)->i32 < ((Value_Int32 *)y)->i32)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
Value *lt_i64(Value *x, Value *y)
{
    if (((Value_Int64 *)x)->i64 < ((Value_Int64 *)y)->i64)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
Value *lt_double(Value *x, Value *y)
{
    if (((Value_Double *)x)->d < ((Value_Double *)y)->d)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
Value *lt_char(Value *x, Value *y)
{
    if (((Value_Char *)x)->c < ((Value_Char *)y)->c)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}

/* gt */
Value *gt_i32(Value *x, Value *y)
{
    if (((Value_Int32 *)x)->i32 > ((Value_Int32 *)y)->i32)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
Value *gt_i64(Value *x, Value *y)
{
    if (((Value_Int64 *)x)->i64 > ((Value_Int64 *)y)->i64)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
Value *gt_double(Value *x, Value *y)
{
    if (((Value_Double *)x)->d > ((Value_Double *)y)->d)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
Value *gt_char(Value *x, Value *y)
{
    if (((Value_Char *)x)->c > ((Value_Char *)y)->c)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}

/* eq */
Value *eq_i32(Value *x, Value *y)
{
    if (((Value_Int32 *)x)->i32 == ((Value_Int32 *)y)->i32)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
Value *eq_i64(Value *x, Value *y)
{
    if (((Value_Int64 *)x)->i64 == ((Value_Int64 *)y)->i64)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
Value *eq_double(Value *x, Value *y)
{
    if (((Value_Double *)x)->d == ((Value_Double *)y)->d)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
Value *eq_char(Value *x, Value *y)
{
    if (((Value_Char *)x)->c == ((Value_Char *)y)->c)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
Value *eq_string(Value *x, Value *y)
{
    if (!strcmp(((Value_String *)x)->str, ((Value_String *)y)->str))
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}

/* lte */
Value *lte_i32(Value *x, Value *y)
{
    if (((Value_Int32 *)x)->i32 <= ((Value_Int32 *)y)->i32)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
Value *lte_i64(Value *x, Value *y)
{
    if (((Value_Int64 *)x)->i64 <= ((Value_Int64 *)y)->i64)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
Value *lte_double(Value *x, Value *y)
{
    if (((Value_Double *)x)->d <= ((Value_Double *)y)->d)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
Value *lte_char(Value *x, Value *y)
{
    if (((Value_Char *)x)->c <= ((Value_Char *)y)->c)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}

/* gte */
Value *gte_i32(Value *x, Value *y)
{
    if (((Value_Int32 *)x)->i32 >= ((Value_Int32 *)y)->i32)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
Value *gte_i64(Value *x, Value *y)
{
    if (((Value_Int64 *)x)->i64 >= ((Value_Int64 *)y)->i64)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
Value *gte_double(Value *x, Value *y)
{
    if (((Value_Double *)x)->d >= ((Value_Double *)y)->d)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
Value *gte_char(Value *x, Value *y)
{
    if (((Value_Char *)x)->c >= ((Value_Char *)y)->c)
    {
        return (Value *)makeInt32(1);
    }
    else
    {
        return (Value *)makeInt32(0);
    }
}
