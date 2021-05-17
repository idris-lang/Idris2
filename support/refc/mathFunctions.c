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
Value *add_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
    mpz_add(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
    return (Value *)retVal;
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
Value *sub_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
    mpz_sub(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
    return (Value *)retVal;
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
Value *negate_Integer(Value *x)
{
    Value_Integer *retVal = makeInteger();
    mpz_neg(retVal->i, ((Value_Integer *)x)->i);
    return (Value *)retVal;
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
Value *mul_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
    mpz_mul(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
    return (Value *)retVal;
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
Value *div_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
    mpz_fdiv_q(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
    return (Value *)retVal;
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
Value *mod_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
    mpz_mod(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
    return (Value *)retVal;
}

/* shiftl */
Value *shiftl_Int(Value *x, Value *y)
{
    return (Value *)makeInt(((Value_Int *)x)->i64 << ((Value_Int *)y)->i64);
}
Value *shiftl_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
    mp_bitcnt_t cnt = (mp_bitcnt_t)mpz_get_ui(((Value_Integer *)y)->i);
    mpz_mul_2exp(retVal->i, ((Value_Integer *)x)->i, cnt);
    return (Value *)retVal;
}

/* shiftr */
Value *shiftr_Int(Value *x, Value *y)
{
    return (Value *)makeInt(((Value_Int *)x)->i64 >> ((Value_Int *)y)->i64);
}
Value *shiftr_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
    mp_bitcnt_t cnt = (mp_bitcnt_t)mpz_get_ui(((Value_Integer *)y)->i);
    mpz_fdiv_q_2exp(retVal->i, ((Value_Integer *)x)->i, cnt);
    return (Value *)retVal;
}

/* and */
Value *and_Int(Value *x, Value *y)
{
    return (Value *)makeInt(((Value_Int *)x)->i64 & ((Value_Int *)y)->i64);
}
Value *and_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
    mpz_and(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
    return (Value *)retVal;
}

/* or */
Value *or_Int(Value *x, Value *y)
{
    return (Value *)makeInt(((Value_Int *)x)->i64 | ((Value_Int *)y)->i64);
}
Value *or_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
    mpz_ior(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
    return (Value *)retVal;
}

/* xor */
Value *xor_Int(Value *x, Value *y)
{
    return (Value *)makeInt(((Value_Int *)x)->i64 ^ ((Value_Int *)y)->i64);
}
Value *xor_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
    mpz_xor(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
    return (Value *)retVal;
}

/* lt */
Value *lt_Int(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int *)x)->i64 < ((Value_Int *)y)->i64);
}
Value *lt_Integer(Value *x, Value *y)
{
    return (Value *)makeBool(
        mpz_cmp(((Value_Integer *)x)->i, ((Value_Integer *)y)->i) < 0
    );
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
Value *gt_Integer(Value *x, Value *y)
{
    return (Value *)makeBool(
        mpz_cmp(((Value_Integer *)x)->i, ((Value_Integer *)y)->i) > 0
    );
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
Value *eq_Integer(Value *x, Value *y)
{
    return (Value *)makeBool(
        mpz_cmp(((Value_Integer *)x)->i, ((Value_Integer *)y)->i) == 0
    );
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
Value *lte_Integer(Value *x, Value *y)
{
    return (Value *)makeBool(
        mpz_cmp(((Value_Integer *)x)->i, ((Value_Integer *)y)->i) <= 0
    );
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
Value *gte_Integer(Value *x, Value *y)
{
    return (Value *)makeBool(
        mpz_cmp(((Value_Integer *)x)->i, ((Value_Integer *)y)->i) >= 0
    );
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
