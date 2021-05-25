#ifndef __MATH_FUNCTIONS_H__
#define __MATH_FUNCTIONS_H__
#include "cBackend.h"
#include <math.h>
#include <gmp.h>

double unpackDouble(Value *d);
Value *believe_me(Value *, Value *, Value *);

/* add */
Value *add_Bits8(Value *x, Value *y);
Value *add_Bits16(Value *x, Value *y);
Value *add_Bits32(Value *x, Value *y);
Value *add_Bits64(Value *x, Value *y);
Value *add_Int(Value *x, Value *y);
Value *add_Integer(Value *x, Value *y);
Value *add_double(Value *x, Value *y);

/* sub */
Value *sub_Bits8(Value *x, Value *y);
Value *sub_Bits16(Value *x, Value *y);
Value *sub_Bits32(Value *x, Value *y);
Value *sub_Bits64(Value *x, Value *y);
Value *sub_Int(Value *x, Value *y);
Value *sub_Integer(Value *x, Value *y);
Value *sub_double(Value *x, Value *y);

/* negate */
Value *negate_Bits8(Value *x);
Value *negate_Bits16(Value *x);
Value *negate_Bits32(Value *x);
Value *negate_Bits64(Value *x);
Value *negate_Int(Value *x);
Value *negate_Integer(Value *x);
Value *negate_double(Value *x);

/* mul */
Value *mul_Bits8(Value *x, Value *y);
Value *mul_Bits16(Value *x, Value *y);
Value *mul_Bits32(Value *x, Value *y);
Value *mul_Bits64(Value *x, Value *y);
Value *mul_Int(Value *x, Value *y);
Value *mul_Integer(Value *x, Value *y);
Value *mul_double(Value *x, Value *y);

/* div */
Value *div_Bits8(Value *x, Value *y);
Value *div_Bits16(Value *x, Value *y);
Value *div_Bits32(Value *x, Value *y);
Value *div_Bits64(Value *x, Value *y);
Value *div_Int(Value *x, Value *y);
Value *div_Integer(Value *x, Value *y);
Value *div_double(Value *x, Value *y);

/* mod */
Value *mod_Bits8(Value *x, Value *y);
Value *mod_Bits16(Value *x, Value *y);
Value *mod_Bits32(Value *x, Value *y);
Value *mod_Bits64(Value *x, Value *y);
Value *mod_Int(Value *x, Value *y);
Value *mod_Integer(Value *x, Value *y);

/* shiftl */
Value *shiftl_Bits8(Value *x, Value *y);
Value *shiftl_Bits16(Value *x, Value *y);
Value *shiftl_Bits32(Value *x, Value *y);
Value *shiftl_Bits64(Value *x, Value *y);
Value *shiftl_Int(Value *x, Value *y);
Value *shiftl_Integer(Value *x, Value *y);

/* shiftr */
Value *shiftr_Bits8(Value *x, Value *y);
Value *shiftr_Bits16(Value *x, Value *y);
Value *shiftr_Bits32(Value *x, Value *y);
Value *shiftr_Bits64(Value *x, Value *y);
Value *shiftr_Int(Value *x, Value *y);
Value *shiftr_Integer(Value *x, Value *y);

/* and */
Value *and_Bits8(Value *x, Value *y);
Value *and_Bits16(Value *x, Value *y);
Value *and_Bits32(Value *x, Value *y);
Value *and_Bits64(Value *x, Value *y);
Value *and_Int(Value *x, Value *y);
Value *and_Integer(Value *x, Value *y);

/* or */
Value *or_Bits8(Value *x, Value *y);
Value *or_Bits16(Value *x, Value *y);
Value *or_Bits32(Value *x, Value *y);
Value *or_Bits64(Value *x, Value *y);
Value *or_Int(Value *x, Value *y);
Value *or_Integer(Value *x, Value *y);

/* xor */
Value *xor_Bits8(Value *x, Value *y);
Value *xor_Bits16(Value *x, Value *y);
Value *xor_Bits32(Value *x, Value *y);
Value *xor_Bits64(Value *x, Value *y);
Value *xor_Int(Value *x, Value *y);
Value *xor_Integer(Value *x, Value *y);

/* lt */
Value *lt_Bits8(Value *x, Value *y);
Value *lt_Bits16(Value *x, Value *y);
Value *lt_Bits32(Value *x, Value *y);
Value *lt_Bits64(Value *x, Value *y);
Value *lt_Int(Value *x, Value *y);
Value *lt_Integer(Value *x, Value *y);
Value *lt_double(Value *x, Value *y);
Value *lt_char(Value *x, Value *y);
Value *lt_string(Value *x, Value *y);

/* gt */
Value *gt_Bits8(Value *x, Value *y);
Value *gt_Bits16(Value *x, Value *y);
Value *gt_Bits32(Value *x, Value *y);
Value *gt_Bits64(Value *x, Value *y);
Value *gt_Int(Value *x, Value *y);
Value *gt_Integer(Value *x, Value *y);
Value *gt_double(Value *x, Value *y);
Value *gt_char(Value *x, Value *y);
Value *gt_string(Value *x, Value *y);

/* eq */
Value *eq_Bits8(Value *x, Value *y);
Value *eq_Bits16(Value *x, Value *y);
Value *eq_Bits32(Value *x, Value *y);
Value *eq_Bits64(Value *x, Value *y);
Value *eq_Int(Value *x, Value *y);
Value *eq_Integer(Value *x, Value *y);
Value *eq_double(Value *x, Value *y);
Value *eq_char(Value *x, Value *y);
Value *eq_string(Value *x, Value *y);

/* lte */
Value *lte_Bits8(Value *x, Value *y);
Value *lte_Bits16(Value *x, Value *y);
Value *lte_Bits32(Value *x, Value *y);
Value *lte_Bits64(Value *x, Value *y);
Value *lte_Int(Value *x, Value *y);
Value *lte_Integer(Value *x, Value *y);
Value *lte_double(Value *x, Value *y);
Value *lte_char(Value *x, Value *y);
Value *lte_string(Value *x, Value *y);

/* gte */
Value *gte_Bits8(Value *x, Value *y);
Value *gte_Bits16(Value *x, Value *y);
Value *gte_Bits32(Value *x, Value *y);
Value *gte_Bits64(Value *x, Value *y);
Value *gte_Int(Value *x, Value *y);
Value *gte_Integer(Value *x, Value *y);
Value *gte_double(Value *x, Value *y);
Value *gte_char(Value *x, Value *y);
Value *gte_string(Value *x, Value *y);
#endif
