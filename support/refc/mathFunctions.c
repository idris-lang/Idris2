#include "mathFunctions.h"
#include "runtime.h"
#include "memoryManagement.h"

double unpackDouble(Value *d)
{
    return ((Value_Double *)d)->d;
}

/* add */
Value *add_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 + ((Value_Bits8 *)y)->ui8);
}
Value *add_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 + ((Value_Bits16 *)y)->ui16);
}
Value *add_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 + ((Value_Bits32 *)y)->ui32);
}
Value *add_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 + ((Value_Bits64 *)y)->ui64);
}
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
Value *sub_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 - ((Value_Bits8 *)y)->ui8);
}
Value *sub_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 - ((Value_Bits16 *)y)->ui16);
}
Value *sub_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 - ((Value_Bits32 *)y)->ui32);
}
Value *sub_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 - ((Value_Bits64 *)y)->ui64);
}
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
Value *negate_Bits8(Value *x)
{
    return (Value *)makeBits8(-((Value_Bits8 *)x)->ui8);
}
Value *negate_Bits16(Value *x)
{
    return (Value *)makeBits16(-((Value_Bits16 *)x)->ui16);
}
Value *negate_Bits32(Value *x)
{
    return (Value *)makeBits32(-((Value_Bits32 *)x)->ui32);
}
Value *negate_Bits64(Value *x)
{
    return (Value *)makeBits64(-((Value_Bits64 *)x)->ui64);
}
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
Value *mul_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 * ((Value_Bits8 *)y)->ui8);
}
Value *mul_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 * ((Value_Bits16 *)y)->ui16);
}
Value *mul_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 * ((Value_Bits32 *)y)->ui32);
}
Value *mul_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 * ((Value_Bits64 *)y)->ui64);
}
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
Value *div_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 / ((Value_Bits8 *)y)->ui8);
}
Value *div_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 / ((Value_Bits16 *)y)->ui16);
}
Value *div_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 / ((Value_Bits32 *)y)->ui32);
}
Value *div_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 / ((Value_Bits64 *)y)->ui64);
}
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
Value *mod_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 % ((Value_Bits8 *)y)->ui8);
}
Value *mod_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 % ((Value_Bits16 *)y)->ui16);
}
Value *mod_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 % ((Value_Bits32 *)y)->ui32);
}
Value *mod_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 % ((Value_Bits64 *)y)->ui64);
}
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
Value *shiftl_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 << ((Value_Bits8 *)y)->ui8);
}
Value *shiftl_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 << ((Value_Bits16 *)y)->ui16);
}
Value *shiftl_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 << ((Value_Bits32 *)y)->ui32);
}
Value *shiftl_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 << ((Value_Bits64 *)y)->ui64);
}
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
Value *shiftr_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 >> ((Value_Bits8 *)y)->ui8);
}
Value *shiftr_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 >> ((Value_Bits16 *)y)->ui16);
}
Value *shiftr_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 >> ((Value_Bits32 *)y)->ui32);
}
Value *shiftr_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 >> ((Value_Bits64 *)y)->ui64);
}
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
Value *and_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 & ((Value_Bits8 *)y)->ui8);
}
Value *and_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 & ((Value_Bits16 *)y)->ui16);
}
Value *and_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 & ((Value_Bits32 *)y)->ui32);
}
Value *and_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 & ((Value_Bits64 *)y)->ui64);
}
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
Value *or_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 | ((Value_Bits8 *)y)->ui8);
}
Value *or_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 | ((Value_Bits16 *)y)->ui16);
}
Value *or_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 | ((Value_Bits32 *)y)->ui32);
}
Value *or_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 | ((Value_Bits64 *)y)->ui64);
}
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
Value *xor_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 ^ ((Value_Bits8 *)y)->ui8);
}
Value *xor_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 ^ ((Value_Bits16 *)y)->ui16);
}
Value *xor_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 ^ ((Value_Bits32 *)y)->ui32);
}
Value *xor_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 ^ ((Value_Bits64 *)y)->ui64);
}
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
Value *lt_Bits8(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits8 *)x)->ui8 < ((Value_Bits8 *)y)->ui8);
}
Value *lt_Bits16(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits16 *)x)->ui16 < ((Value_Bits16 *)y)->ui16);
}
Value *lt_Bits32(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits32 *)x)->ui32 < ((Value_Bits32 *)y)->ui32);
}
Value *lt_Bits64(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits64 *)x)->ui64 < ((Value_Bits64 *)y)->ui64);
}
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
Value *gt_Bits8(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits8 *)x)->ui8 > ((Value_Bits8 *)y)->ui8);
}
Value *gt_Bits16(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits16 *)x)->ui16 > ((Value_Bits16 *)y)->ui16);
}
Value *gt_Bits32(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits32 *)x)->ui32 > ((Value_Bits32 *)y)->ui32);
}
Value *gt_Bits64(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits64 *)x)->ui64 > ((Value_Bits64 *)y)->ui64);
}
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
Value *eq_Bits8(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits8 *)x)->ui8 == ((Value_Bits8 *)y)->ui8);
}
Value *eq_Bits16(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits16 *)x)->ui16 == ((Value_Bits16 *)y)->ui16);
}
Value *eq_Bits32(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits32 *)x)->ui32 == ((Value_Bits32 *)y)->ui32);
}
Value *eq_Bits64(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits64 *)x)->ui64 == ((Value_Bits64 *)y)->ui64);
}
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
Value *lte_Bits8(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits8 *)x)->ui8 <= ((Value_Bits8 *)y)->ui8);
}
Value *lte_Bits16(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits16 *)x)->ui16 <= ((Value_Bits16 *)y)->ui16);
}
Value *lte_Bits32(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits32 *)x)->ui32 <= ((Value_Bits32 *)y)->ui32);
}
Value *lte_Bits64(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits64 *)x)->ui64 <= ((Value_Bits64 *)y)->ui64);
}
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
Value *gte_Bits8(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits8 *)x)->ui8 >= ((Value_Bits8 *)y)->ui8);
}
Value *gte_Bits16(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits16 *)x)->ui16 >= ((Value_Bits16 *)y)->ui16);
}
Value *gte_Bits32(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits32 *)x)->ui32 >= ((Value_Bits32 *)y)->ui32);
}
Value *gte_Bits64(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits64 *)x)->ui64 >= ((Value_Bits64 *)y)->ui64);
}
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
