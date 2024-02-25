#pragma once

#include "cBackend.h"
#include <gmp.h>
#include <math.h>

#define idris2_binop(ty, op, l, r)                                             \
  ((Value *)idris2_mk##ty(idris2_vp_to_##ty(l) op idris2_vp_to_##ty(r)))

/* add */
#define idris2_add_Bits8(l, r) (idris2_binop(Bits8, +, l, r))
#define idris2_add_Bits16(l, r) (idris2_binop(Bits16, +, l, r))
#define idris2_add_Bits32(l, r) (idris2_binop(Bits32, +, l, r))
#define idris2_add_Bits64(l, r) (idris2_binop(Bits64, +, l, r))
#define idris2_add_Int8(l, r) (idris2_binop(Int8, +, l, r))
#define idris2_add_Int16(l, r) (idris2_binop(Int16, +, l, r))
#define idris2_add_Int32(l, r) (idris2_binop(Int32, +, l, r))
#define idris2_add_Int64(l, r) (idris2_binop(Int64, +, l, r))
Value *idris2_add_Integer(Value *x, Value *y);
#define idris2_add_Double(l, r) (idris2_binop(Double, +, l, r))

/* sub */
#define idris2_sub_Bits8(l, r) (idris2_binop(Bits8, -, l, r))
#define idris2_sub_Bits16(l, r) (idris2_binop(Bits16, -, l, r))
#define idris2_sub_Bits32(l, r) (idris2_binop(Bits32, -, l, r))
#define idris2_sub_Bits64(l, r) (idris2_binop(Bits64, -, l, r))
#define idris2_sub_Int8(l, r) (idris2_binop(Int8, -, l, r))
#define idris2_sub_Int16(l, r) (idris2_binop(Int16, -, l, r))
#define idris2_sub_Int32(l, r) (idris2_binop(Int32, -, l, r))
#define idris2_sub_Int64(l, r) (idris2_binop(Int64, -, l, r))
Value *idris2_sub_Integer(Value *x, Value *y);
#define idris2_sub_Double(l, r) (idris2_binop(Double, -, l, r))

/* negate */
#define idris2_nagate_Int8(x) (idris2_mkInt8(-(idris2_vp_to_Int8(x))))
#define idris2_nagate_Int16(x) (idris2_mkInt16(-(idris2_vp_to_Int16(x))))
#define idris2_nagate_Int32(x) (idris2_mkInt32(-(idris2_vp_to_Int32(x))))
#define idris2_nagate_Int64(x) (idris2_mkInt64(-(idris2_vp_to_Int64(x))))
Value *idris2_negate_Integer(Value *x);
#define idris2_nagate_Double(x) (idris2_mkDouble(-(idris2_vp_to_Double(x))))

/* mul */
#define idris2_mul_Bits8(l, r) (idris2_binop(Bits8, *, l, r))
#define idris2_mul_Bits16(l, r) (idris2_binop(Bits16, *, l, r))
#define idris2_mul_Bits32(l, r) (idris2_binop(Bits32, *, l, r))
#define idris2_mul_Bits64(l, r) (idris2_binop(Bits64, *, l, r))
#define idris2_mul_Int8(l, r) (idris2_binop(Int8, *, l, r))
#define idris2_mul_Int16(l, r) (idris2_binop(Int16, *, l, r))
#define idris2_mul_Int32(l, r) (idris2_binop(Int32, *, l, r))
#define idris2_mul_Int64(l, r) (idris2_binop(Int64, *, l, r))
Value *idris2_mul_Integer(Value *x, Value *y);
#define idris2_mul_Double(l, r) (idris2_binop(Double, *, l, r))

/* div */
#define idris2_div_Bits8(l, r) (idris2_binop(Bits8, /, l, r))
#define idris2_div_Bits16(l, r) (idris2_binop(Bits16, /, l, r))
#define idris2_div_Bits32(l, r) (idris2_binop(Bits32, /, l, r))
#define idris2_div_Bits64(l, r) (idris2_binop(Bits64, /, l, r))
Value *idris2_div_Int8(Value *x, Value *y);
Value *idris2_div_Int16(Value *x, Value *y);
Value *idris2_div_Int32(Value *x, Value *y);
Value *idris2_div_Int64(Value *x, Value *y);
Value *idris2_div_Integer(Value *x, Value *y);
#define idris2_div_Double(l, r) (idris2_binop(Double, /, l, r))

/* mod */
#define idris2_mod_Bits8(l, r) (idris2_binop(Bits8, %, l, r))
#define idris2_mod_Bits16(l, r) (idris2_binop(Bits16, %, l, r))
#define idris2_mod_Bits32(l, r) (idris2_binop(Bits32, %, l, r))
#define idris2_mod_Bits64(l, r) (idris2_binop(Bits64, %, l, r))
Value *idris2_mod_Int8(Value *x, Value *y);
Value *idris2_mod_Int16(Value *x, Value *y);
Value *idris2_mod_Int32(Value *x, Value *y);
Value *idris2_mod_Int64(Value *x, Value *y);
Value *idris2_mod_Integer(Value *x, Value *y);

/* shiftl */
#define idris2_shiftl_Bits8(l, r) (idris2_binop(Bits8, <<, l, r))
#define idris2_shiftl_Bits16(l, r) (idris2_binop(Bits16, <<, l, r))
#define idris2_shiftl_Bits32(l, r) (idris2_binop(Bits32, <<, l, r))
#define idris2_shiftl_Bits64(l, r) (idris2_binop(Bits64, <<, l, r))
#define idris2_shiftl_Int8(l, r) (idris2_binop(Int8, <<, l, r))
#define idris2_shiftl_Int16(l, r) (idris2_binop(Int16, <<, l, r))
#define idris2_shiftl_Int32(l, r) (idris2_binop(Int32, <<, l, r))
#define idris2_shiftl_Int64(l, r) (idris2_binop(Int64, <<, l, r))
Value *idris2_shiftl_Integer(Value *x, Value *y);

/* shiftr */
#define idris2_shiftr_Bits8(l, r) (idris2_binop(Bits8, >>, l, r))
#define idris2_shiftr_Bits16(l, r) (idris2_binop(Bits16, >>, l, r))
#define idris2_shiftr_Bits32(l, r) (idris2_binop(Bits32, >>, l, r))
#define idris2_shiftr_Bits64(l, r) (idris2_binop(Bits64, >>, l, r))
#define idris2_shiftr_Int8(l, r) (idris2_binop(Int8, >>, l, r))
#define idris2_shiftr_Int16(l, r) (idris2_binop(Int16, >>, l, r))
#define idris2_shiftr_Int32(l, r) (idris2_binop(Int32, >>, l, r))
#define idris2_shiftr_Int64(l, r) (idris2_binop(Int64, >>, l, r))
Value *idris2_shiftr_Integer(Value *x, Value *y);

/* and */
#define idris2_and_Bits8(l, r) (idris2_binop(Bits8, &, l, r))
#define idris2_and_Bits16(l, r) (idris2_binop(Bits16, &, l, r))
#define idris2_and_Bits32(l, r) (idris2_binop(Bits32, &, l, r))
#define idris2_and_Bits64(l, r) (idris2_binop(Bits64, &, l, r))
#define idris2_and_Int8(l, r) (idris2_binop(Int8, &, l, r))
#define idris2_and_Int16(l, r) (idris2_binop(Int16, &, l, r))
#define idris2_and_Int32(l, r) (idris2_binop(Int32, &, l, r))
#define idris2_and_Int64(l, r) (idris2_binop(Int64, &, l, r))
Value *idris2_and_Integer(Value *x, Value *y);

/* or */
#define idris2_or_Bits8(l, r) (idris2_binop(Bits8, |, l, r))
#define idris2_or_Bits16(l, r) (idris2_binop(Bits16, |, l, r))
#define idris2_or_Bits32(l, r) (idris2_binop(Bits32, |, l, r))
#define idris2_or_Bits64(l, r) (idris2_binop(Bits64, |, l, r))
#define idris2_or_Int8(l, r) (idris2_binop(Int8, |, l, r))
#define idris2_or_Int16(l, r) (idris2_binop(Int16, |, l, r))
#define idris2_or_Int32(l, r) (idris2_binop(Int32, |, l, r))
#define idris2_or_Int64(l, r) (idris2_binop(Int64, |, l, r))
Value *idris2_or_Integer(Value *x, Value *y);

/* xor */
#define idris2_xor_Bits8(l, r) (idris2_binop(Bits8, ^, l, r))
#define idris2_xor_Bits16(l, r) (idris2_binop(Bits16, ^, l, r))
#define idris2_xor_Bits32(l, r) (idris2_binop(Bits32, ^, l, r))
#define idris2_xor_Bits64(l, r) (idris2_binop(Bits64, ^, l, r))
#define idris2_xor_Int8(l, r) (idris2_binop(Int8, ^, l, r))
#define idris2_xor_Int16(l, r) (idris2_binop(Int16, ^, l, r))
#define idris2_xor_Int32(l, r) (idris2_binop(Int32, ^, l, r))
#define idris2_xor_Int64(l, r) (idris2_binop(Int64, ^, l, r))
Value *idris2_xor_Integer(Value *x, Value *y);

#define idris2_cmpop(ty, op, l, r)                                             \
  (idris2_mkBool((idris2_vp_to_##ty(l) op idris2_vp_to_##ty(r)) ? 1 : 0))

/* lt */
#define idris2_lt_Bits8(l, r) (idris2_cmpop(Bits8, <, l, r))
#define idris2_lt_Bits16(l, r) (idris2_cmpop(Bits16, <, l, r))
#define idris2_lt_Bits32(l, r) (idris2_cmpop(Bits32, <, l, r))
#define idris2_lt_Bits64(l, r) (idris2_cmpop(Bits64, <, l, r))
#define idris2_lt_Int8(l, r) (idris2_cmpop(Int8, <, l, r))
#define idris2_lt_Int16(l, r) (idris2_cmpop(Int16, <, l, r))
#define idris2_lt_Int32(l, r) (idris2_cmpop(Int32, <, l, r))
#define idris2_lt_Int64(l, r) (idris2_cmpop(Int64, <, l, r))
#define idris2_lt_Integer(l, r)                                                \
  (idris2_mkBool(                                                              \
      mpz_cmp(((Value_Integer *)(l))->i, ((Value_Integer *)(r))->i) < 0))
#define idris2_lt_Double(l, r) (idris2_cmpop(Double, <, l, r))
#define idris2_lt_Char(l, r) (idris2_cmpop(Char, <, l, r))
#define idris2_lt_string(l, r)                                                 \
  (idris2_mkBool(                                                              \
      strcmp(((Value_String *)(l))->str, ((Value_String *)(r))->str) < 0))

/* gt */
#define idris2_gt_Bits8(l, r) (idris2_cmpop(Bits8, >, l, r))
#define idris2_gt_Bits16(l, r) (idris2_cmpop(Bits16, >, l, r))
#define idris2_gt_Bits32(l, r) (idris2_cmpop(Bits32, >, l, r))
#define idris2_gt_Bits64(l, r) (idris2_cmpop(Bits64, >, l, r))
#define idris2_gt_Int8(l, r) (idris2_cmpop(Int8, >, l, r))
#define idris2_gt_Int16(l, r) (idris2_cmpop(Int16, >, l, r))
#define idris2_gt_Int32(l, r) (idris2_cmpop(Int32, >, l, r))
#define idris2_gt_Int64(l, r) (idris2_cmpop(Int64, >, l, r))
#define idris2_gt_Integer(l, r)                                                \
  (idris2_mkBool(                                                              \
      mpz_cmp(((Value_Integer *)(l))->i, ((Value_Integer *)(r))->i) > 0))
#define idris2_gt_Double(l, r) (idris2_cmpop(Double, >, l, r))
#define idris2_gt_Char(l, r) (idris2_cmpop(Char, >, l, r))
#define idris2_gt_string(l, r)                                                 \
  (idris2_mkBool(                                                              \
      strcmp(((Value_String *)(l))->str, ((Value_String *)(r))->str) > 0))

/* eq */
#define idris2_eq_Bits8(l, r) (idris2_cmpop(Bits8, ==, l, r))
#define idris2_eq_Bits16(l, r) (idris2_cmpop(Bits16, ==, l, r))
#define idris2_eq_Bits32(l, r) (idris2_cmpop(Bits32, ==, l, r))
#define idris2_eq_Bits64(l, r) (idris2_cmpop(Bits64, ==, l, r))
#define idris2_eq_Int8(l, r) (idris2_cmpop(Int8, ==, l, r))
#define idris2_eq_Int16(l, r) (idris2_cmpop(Int16, ==, l, r))
#define idris2_eq_Int32(l, r) (idris2_cmpop(Int32, ==, l, r))
#define idris2_eq_Int64(l, r) (idris2_cmpop(Int64, ==, l, r))
#define idris2_eq_Integer(l, r)                                                \
  (idris2_mkBool(                                                              \
      mpz_cmp(((Value_Integer *)(l))->i, ((Value_Integer *)(r))->i) == 0))
#define idris2_eq_Double(l, r) (idris2_cmpop(Double, ==, l, r))
#define idris2_eq_Char(l, r) (idris2_cmpop(Char, ==, l, r))
#define idris2_eq_string(l, r)                                                 \
  (idris2_mkBool(                                                              \
      strcmp(((Value_String *)(l))->str, ((Value_String *)(r))->str) == 0))

/* lte */
#define idris2_lte_Bits8(l, r) (idris2_cmpop(Bits8, <=, l, r))
#define idris2_lte_Bits16(l, r) (idris2_cmpop(Bits16, <=, l, r))
#define idris2_lte_Bits32(l, r) (idris2_cmpop(Bits32, <=, l, r))
#define idris2_lte_Bits64(l, r) (idris2_cmpop(Bits64, <=, l, r))
#define idris2_lte_Int8(l, r) (idris2_cmpop(Int8, <=, l, r))
#define idris2_lte_Int16(l, r) (idris2_cmpop(Int16, <=, l, r))
#define idris2_lte_Int32(l, r) (idris2_cmpop(Int32, <=, l, r))
#define idris2_lte_Int64(l, r) (idris2_cmpop(Int64, <=, l, r))
#define idris2_lte_Integer(l, r)                                               \
  (idris2_mkBool(                                                              \
      mpz_cmp(((Value_Integer *)(l))->i, ((Value_Integer *)(r))->i) <= 0))
#define idris2_lte_Double(l, r) (idris2_cmpop(Double, <=, l, r))
#define idris2_lte_Char(l, r) (idris2_cmpop(Char, <=, l, r))
#define idris2_lte_string(l, r)                                                \
  (idris2_mkBool(                                                              \
      strcmp(((Value_String *)(l))->str, ((Value_String *)(r))->str) <= 0))

/* gte */
#define idris2_gte_Bits8(l, r) (idris2_cmpop(Bits8, >=, l, r))
#define idris2_gte_Bits16(l, r) (idris2_cmpop(Bits16, >=, l, r))
#define idris2_gte_Bits32(l, r) (idris2_cmpop(Bits32, >=, l, r))
#define idris2_gte_Bits64(l, r) (idris2_cmpop(Bits64, >=, l, r))
#define idris2_gte_Int8(l, r) (idris2_cmpop(Int8, >=, l, r))
#define idris2_gte_Int16(l, r) (idris2_cmpop(Int16, >=, l, r))
#define idris2_gte_Int32(l, r) (idris2_cmpop(Int32, >=, l, r))
#define idris2_gte_Int64(l, r) (idris2_cmpop(Int64, >=, l, r))
#define idris2_gte_Integer(l, r)                                               \
  (idris2_mkBool(                                                              \
      mpz_cmp(((Value_Integer *)(l))->i, ((Value_Integer *)(r))->i) >= 0))
#define idris2_gte_Double(l, r) (idris2_cmpop(Double, >=, l, r))
#define idris2_gte_Char(l, r) (idris2_cmpop(Char, >=, l, r))
#define idris2_gte_string(l, r)                                                \
  (idris2_mkBool(                                                              \
      strcmp(((Value_String *)(l))->str, ((Value_String *)(r))->str) >= 0))
