#ifndef __MATH_FUNCTIONS_H__
#define __MATH_FUNCTIONS_H__
#include "cBackend.h"
#include <math.h>

double unpackDouble(Value *d);
Value *believe_me(Value *, Value *, Value *);

/* add */
Value *add_i32(Value *x, Value *y);
Value *add_i64(Value *x, Value *y);
Value *add_double(Value *x, Value *y);

/* sub */
Value *sub_i32(Value *x, Value *y);
Value *sub_i64(Value *x, Value *y);
Value *sub_double(Value *x, Value *y);

/* negate */
Value *negate_i32(Value *x);
Value *negate_i64(Value *x);
Value *negate_double(Value *x);

/* mul */
Value *mul_i32(Value *x, Value *y);
Value *mul_i64(Value *x, Value *y);
Value *mul_double(Value *x, Value *y);

/* div */
Value *div_i32(Value *x, Value *y);
Value *div_i64(Value *x, Value *y);
Value *div_double(Value *x, Value *y);

/* mod */
Value *mod_i32(Value *x, Value *y);
Value *mod_i64(Value *x, Value *y);

/* shiftl */
Value *shiftl_i32(Value *x, Value *y);
Value *shiftl_i64(Value *x, Value *y);

/* shiftr */
Value *shiftr_i32(Value *x, Value *y);
Value *shiftr_i64(Value *x, Value *y);

/* and */
Value *and_i32(Value *x, Value *y);
Value *and_i64(Value *x, Value *y);

/* or */
Value *or_i32(Value *x, Value *y);
Value *or_i64(Value *x, Value *y);

/* xor */
Value *xor_i32(Value *x, Value *y);
Value *xor_i64(Value *x, Value *y);

/* lt */
Value *lt_i32(Value *x, Value *y);
Value *lt_i64(Value *x, Value *y);
Value *lt_double(Value *x, Value *y);
Value *lt_char(Value *x, Value *y);
Value *lt_string(Value *x, Value *y);

/* gt */
Value *gt_i32(Value *x, Value *y);
Value *gt_i64(Value *x, Value *y);
Value *gt_double(Value *x, Value *y);
Value *gt_char(Value *x, Value *y);
Value *gt_string(Value *x, Value *y);

/* eq */
Value *eq_i32(Value *x, Value *y);
Value *eq_i64(Value *x, Value *y);
Value *eq_double(Value *x, Value *y);
Value *eq_char(Value *x, Value *y);
Value *eq_string(Value *x, Value *y);

/* lte */
Value *lte_i32(Value *x, Value *y);
Value *lte_i64(Value *x, Value *y);
Value *lte_double(Value *x, Value *y);
Value *lte_char(Value *x, Value *y);
Value *lte_string(Value *x, Value *y);

/* gte */
Value *gte_i32(Value *x, Value *y);
Value *gte_i64(Value *x, Value *y);
Value *gte_double(Value *x, Value *y);
Value *gte_char(Value *x, Value *y);
Value *gte_string(Value *x, Value *y);
#endif
