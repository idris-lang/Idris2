#ifndef __MATH_FUNCTIONS_H__
#define __MATH_FUNCTIONS_H__
#include "cBackend.h"
#include <math.h>
#include <gmp.h>

double unpackDouble(Value *d);
Value *believe_me(Value *, Value *, Value *);

/* add */
Value *add_Int(Value *x, Value *y);
Value *add_Integer(Value *x, Value *y);
Value *add_double(Value *x, Value *y);

/* sub */
Value *sub_Int(Value *x, Value *y);
Value *sub_Integer(Value *x, Value *y);
Value *sub_double(Value *x, Value *y);

/* negate */
Value *negate_Int(Value *x);
Value *negate_Integer(Value *x);
Value *negate_double(Value *x);

/* mul */
Value *mul_Int(Value *x, Value *y);
Value *mul_Integer(Value *x, Value *y);
Value *mul_double(Value *x, Value *y);

/* div */
Value *div_Int(Value *x, Value *y);
Value *div_Integer(Value *x, Value *y);
Value *div_double(Value *x, Value *y);

/* mod */
Value *mod_Int(Value *x, Value *y);
Value *mod_Integer(Value *x, Value *y);

/* shiftl */
Value *shiftl_Int(Value *x, Value *y);
Value *shiftl_Integer(Value *x, Value *y);

/* shiftr */
Value *shiftr_Int(Value *x, Value *y);
Value *shiftr_Integer(Value *x, Value *y);

/* and */
Value *and_Int(Value *x, Value *y);
Value *and_Integer(Value *x, Value *y);

/* or */
Value *or_Int(Value *x, Value *y);
Value *or_Integer(Value *x, Value *y);

/* xor */
Value *xor_Int(Value *x, Value *y);
Value *xor_Integer(Value *x, Value *y);

/* lt */
Value *lt_Int(Value *x, Value *y);
Value *lt_Integer(Value *x, Value *y);
Value *lt_double(Value *x, Value *y);
Value *lt_char(Value *x, Value *y);
Value *lt_string(Value *x, Value *y);

/* gt */
Value *gt_Int(Value *x, Value *y);
Value *gt_Integer(Value *x, Value *y);
Value *gt_double(Value *x, Value *y);
Value *gt_char(Value *x, Value *y);
Value *gt_string(Value *x, Value *y);

/* eq */
Value *eq_Int(Value *x, Value *y);
Value *eq_Integer(Value *x, Value *y);
Value *eq_double(Value *x, Value *y);
Value *eq_char(Value *x, Value *y);
Value *eq_string(Value *x, Value *y);

/* lte */
Value *lte_Int(Value *x, Value *y);
Value *lte_Integer(Value *x, Value *y);
Value *lte_double(Value *x, Value *y);
Value *lte_char(Value *x, Value *y);
Value *lte_string(Value *x, Value *y);

/* gte */
Value *gte_Int(Value *x, Value *y);
Value *gte_Integer(Value *x, Value *y);
Value *gte_double(Value *x, Value *y);
Value *gte_char(Value *x, Value *y);
Value *gte_string(Value *x, Value *y);
#endif
