#pragma once

#include "cBackend.h"
#include <gmp.h>
#include <math.h>

#define idris2_binop(ty, op, l, r)                                             \
  ((Value *)idris2_mk##ty(idris2_vp_to_##ty(l) op idris2_vp_to_##ty(r)))

/* add */
#define add_Bits8(l, r) (idris2_binop(Bits8, +, l, r))
#define add_Bits16(l, r) (idris2_binop(Bits16, +, l, r))
#define add_Bits32(l, r) (idris2_binop(Bits32, +, l, r))
#define add_Bits64(l, r) (idris2_binop(Bits64, +, l, r))
#define add_Int8(l, r) (idris2_binop(Int8, +, l, r))
#define add_Int16(l, r) (idris2_binop(Int16, +, l, r))
#define add_Int32(l, r) (idris2_binop(Int32, +, l, r))
#define add_Int64(l, r) (idris2_binop(Int64, +, l, r))
Value *add_Integer(Value *x, Value *y);
#define add_Double(l, r) (idris2_binop(Double, +, l, r))

/* sub */
#define sub_Bits8(l, r) (idris2_binop(Bits8, -, l, r))
#define sub_Bits16(l, r) (idris2_binop(Bits16, -, l, r))
#define sub_Bits32(l, r) (idris2_binop(Bits32, -, l, r))
#define sub_Bits64(l, r) (idris2_binop(Bits64, -, l, r))
#define sub_Int8(l, r) (idris2_binop(Int8, -, l, r))
#define sub_Int16(l, r) (idris2_binop(Int16, -, l, r))
#define sub_Int32(l, r) (idris2_binop(Int32, -, l, r))
#define sub_Int64(l, r) (idris2_binop(Int64, -, l, r))
Value *sub_Integer(Value *x, Value *y);
#define sub_Double(l, r) (idris2_binop(Double, -, l, r))

/* negate */
#define nagate_Int8(x) (idris2_mkInt8(-(idris2_vp_to_Int8(x))))
#define nagate_Int16(x) (idris2_mkInt16(-(idris2_vp_to_Int16(x))))
#define nagate_Int32(x) (idris2_mkInt32(-(idris2_vp_to_Int32(x))))
#define nagate_Int64(x) (idris2_mkInt64(-(idris2_vp_to_Int64(x))))
Value *negate_Integer(Value *x);
#define nagate_Double(x) (idris2_mkDouble(-(idris2_vp_to_Double(x))))

/* mul */
#define mul_Bits8(l, r) (idris2_binop(Bits8, *, l, r))
#define mul_Bits16(l, r) (idris2_binop(Bits16, *, l, r))
#define mul_Bits32(l, r) (idris2_binop(Bits32, *, l, r))
#define mul_Bits64(l, r) (idris2_binop(Bits64, *, l, r))
#define mul_Int8(l, r) (idris2_binop(Int8, *, l, r))
#define mul_Int16(l, r) (idris2_binop(Int16, *, l, r))
#define mul_Int32(l, r) (idris2_binop(Int32, *, l, r))
#define mul_Int64(l, r) (idris2_binop(Int64, *, l, r))
Value *mul_Integer(Value *x, Value *y);
#define mul_Double(l, r) (idris2_binop(Double, *, l, r))

/* div */
#define div_Bits8(l, r) (idris2_binop(Bits8, /, l, r))
#define div_Bits16(l, r) (idris2_binop(Bits16, /, l, r))
#define div_Bits32(l, r) (idris2_binop(Bits32, /, l, r))
#define div_Bits64(l, r) (idris2_binop(Bits64, /, l, r))
Value *div_Int8(Value *x, Value *y);
Value *div_Int16(Value *x, Value *y);
Value *div_Int32(Value *x, Value *y);
Value *div_Int64(Value *x, Value *y);
Value *div_Integer(Value *x, Value *y);
#define div_Double(l, r) (idris2_binop(Double, /, l, r))

/* mod */
#define mod_Bits8(l, r) (idris2_binop(Bits8, %, l, r))
#define mod_Bits16(l, r) (idris2_binop(Bits16, %, l, r))
#define mod_Bits32(l, r) (idris2_binop(Bits32, %, l, r))
#define mod_Bits64(l, r) (idris2_binop(Bits64, %, l, r))
Value *mod_Int8(Value *x, Value *y);
Value *mod_Int16(Value *x, Value *y);
Value *mod_Int32(Value *x, Value *y);
Value *mod_Int64(Value *x, Value *y);
Value *mod_Integer(Value *x, Value *y);

/* shiftl */
/* shift Op of idris2 has rediculus signature that (<<), (>>): a -> a -> a .
   stay calm, its should a -> Bits8 -> a ! Did you say intX_t have 2^X bits? no.
   its just X bits. Or, does your PC have 65536bit processor!? Mr.John Titor? */
#define shiftl_Bits8(l, r) (idris2_binop(Bits8, <<, l, r))
#define shiftl_Bits16(l, r) (idris2_binop(Bits16, <<, l, r))
#define shiftl_Bits32(l, r) (idris2_binop(Bits32, <<, l, r))
#define shiftl_Bits64(l, r) (idris2_binop(Bits64, <<, l, r))
#define shiftl_Int8(l, r) (idris2_binop(Int8, <<, l, r))
#define shiftl_Int16(l, r) (idris2_binop(Int16, <<, l, r))
#define shiftl_Int32(l, r) (idris2_binop(Int32, <<, l, r))
#define shiftl_Int64(l, r) (idris2_binop(Int64, <<, l, r))
Value *shiftl_Integer(Value *x, Value *y);

/* shiftr */
#define shiftr_Bits8(l, r) (idris2_binop(Bits8, >>, l, r))
#define shiftr_Bits16(l, r) (idris2_binop(Bits16, >>, l, r))
#define shiftr_Bits32(l, r) (idris2_binop(Bits32, >>, l, r))
#define shiftr_Bits64(l, r) (idris2_binop(Bits64, >>, l, r))
#define shiftr_Int8(l, r) (idris2_binop(Int8, >>, l, r))
#define shiftr_Int16(l, r) (idris2_binop(Int16, >>, l, r))
#define shiftr_Int32(l, r) (idris2_binop(Int32, >>, l, r))
#define shiftr_Int64(l, r) (idris2_binop(Int64, >>, l, r))
Value *shiftr_Integer(Value *x, Value *y);

/* and */
#define and_Bits8(l, r) (idris2_binop(Bits8, &, l, r))
#define and_Bits16(l, r) (idris2_binop(Bits16, &, l, r))
#define and_Bits32(l, r) (idris2_binop(Bits32, &, l, r))
#define and_Bits64(l, r) (idris2_binop(Bits64, &, l, r))
#define and_Int8(l, r) (idris2_binop(Int8, &, l, r))
#define and_Int16(l, r) (idris2_binop(Int16, &, l, r))
#define and_Int32(l, r) (idris2_binop(Int32, &, l, r))
#define and_Int64(l, r) (idris2_binop(Int64, &, l, r))
Value *and_Integer(Value *x, Value *y);

/* or */
#define or_Bits8(l, r) (idris2_binop(Bits8, |, l, r))
#define or_Bits16(l, r) (idris2_binop(Bits16, |, l, r))
#define or_Bits32(l, r) (idris2_binop(Bits32, |, l, r))
#define or_Bits64(l, r) (idris2_binop(Bits64, |, l, r))
#define or_Int8(l, r) (idris2_binop(Int8, |, l, r))
#define or_Int16(l, r) (idris2_binop(Int16, |, l, r))
#define or_Int32(l, r) (idris2_binop(Int32, |, l, r))
#define or_Int64(l, r) (idris2_binop(Int64, |, l, r))
Value *or_Integer(Value *x, Value *y);

/* xor */
#define xor_Bits8(l, r) (idris2_binop(Bits8, ^, l, r))
#define xor_Bits16(l, r) (idris2_binop(Bits16, ^, l, r))
#define xor_Bits32(l, r) (idris2_binop(Bits32, ^, l, r))
#define xor_Bits64(l, r) (idris2_binop(Bits64, ^, l, r))
#define xor_Int8(l, r) (idris2_binop(Int8, ^, l, r))
#define xor_Int16(l, r) (idris2_binop(Int16, ^, l, r))
#define xor_Int32(l, r) (idris2_binop(Int32, ^, l, r))
#define xor_Int64(l, r) (idris2_binop(Int64, ^, l, r))
Value *xor_Integer(Value *x, Value *y);

#define idris2_cmpop(ty, op, l, r)                                             \
  (idris2_mkBool((idris2_vp_to_##ty(l) op idris2_vp_to_##ty(r)) ? 1 : 0))

/* lt */
#define lt_Bits8(l, r) (idris2_cmpop(Bits8, <, l, r))
#define lt_Bits16(l, r) (idris2_cmpop(Bits16, <, l, r))
#define lt_Bits32(l, r) (idris2_cmpop(Bits32, <, l, r))
#define lt_Bits64(l, r) (idris2_cmpop(Bits64, <, l, r))
#define lt_Int8(l, r) (idris2_cmpop(Int8, <, l, r))
#define lt_Int16(l, r) (idris2_cmpop(Int16, <, l, r))
#define lt_Int32(l, r) (idris2_cmpop(Int32, <, l, r))
#define lt_Int64(l, r) (idris2_cmpop(Int64, <, l, r))
#define lt_Integer(l, r)                                                       \
  (idris2_mkBool(                                                              \
      mpz_cmp(((Value_Integer *)(l))->i, ((Value_Integer *)(r))->i) < 0))
#define lt_Double(l, r) (idris2_cmpop(Double, <, l, r))
#define lt_Char(l, r) (idris2_cmpop(Char, <, l, r))
#define lt_string(l, r)                                                        \
  (idris2_mkBool(                                                              \
      strcmp(((Value_String *)(l))->str, ((Value_String *)(r))->str) < 0))

/* gt */
#define gt_Bits8(l, r) (idris2_cmpop(Bits8, >, l, r))
#define gt_Bits16(l, r) (idris2_cmpop(Bits16, >, l, r))
#define gt_Bits32(l, r) (idris2_cmpop(Bits32, >, l, r))
#define gt_Bits64(l, r) (idris2_cmpop(Bits64, >, l, r))
#define gt_Int8(l, r) (idris2_cmpop(Int8, >, l, r))
#define gt_Int16(l, r) (idris2_cmpop(Int16, >, l, r))
#define gt_Int32(l, r) (idris2_cmpop(Int32, >, l, r))
#define gt_Int64(l, r) (idris2_cmpop(Int64, >, l, r))
#define gt_Integer(l, r)                                                       \
  (idris2_mkBool(                                                              \
      mpz_cmp(((Value_Integer *)(l))->i, ((Value_Integer *)(r))->i) > 0))
#define gt_Double(l, r) (idris2_cmpop(Double, >, l, r))
#define gt_Char(l, r) (idris2_cmpop(Char, >, l, r))
#define gt_string(l, r)                                                        \
  (idris2_mkBool(                                                              \
      strcmp(((Value_String *)(l))->str, ((Value_String *)(r))->str) > 0))

/* eq */
#define eq_Bits8(l, r) (idris2_cmpop(Bits8, ==, l, r))
#define eq_Bits16(l, r) (idris2_cmpop(Bits16, ==, l, r))
#define eq_Bits32(l, r) (idris2_cmpop(Bits32, ==, l, r))
#define eq_Bits64(l, r) (idris2_cmpop(Bits64, ==, l, r))
#define eq_Int8(l, r) (idris2_cmpop(Int8, ==, l, r))
#define eq_Int16(l, r) (idris2_cmpop(Int16, ==, l, r))
#define eq_Int32(l, r) (idris2_cmpop(Int32, ==, l, r))
#define eq_Int64(l, r) (idris2_cmpop(Int64, ==, l, r))
#define eq_Integer(l, r)                                                       \
  (idris2_mkBool(                                                              \
      mpz_cmp(((Value_Integer *)(l))->i, ((Value_Integer *)(r))->i) == 0))
#define eq_Double(l, r) (idris2_cmpop(Double, ==, l, r))
#define eq_Char(l, r) (idris2_cmpop(Char, ==, l, r))
#define eq_string(l, r)                                                        \
  (idris2_mkBool(                                                              \
      strcmp(((Value_String *)(l))->str, ((Value_String *)(r))->str) == 0))

/* lte */
#define lte_Bits8(l, r) (idris2_cmpop(Bits8, <=, l, r))
#define lte_Bits16(l, r) (idris2_cmpop(Bits16, <=, l, r))
#define lte_Bits32(l, r) (idris2_cmpop(Bits32, <=, l, r))
#define lte_Bits64(l, r) (idris2_cmpop(Bits64, <=, l, r))
#define lte_Int8(l, r) (idris2_cmpop(Int8, <=, l, r))
#define lte_Int16(l, r) (idris2_cmpop(Int16, <=, l, r))
#define lte_Int32(l, r) (idris2_cmpop(Int32, <=, l, r))
#define lte_Int64(l, r) (idris2_cmpop(Int64, <=, l, r))
#define lte_Integer(l, r)                                                      \
  (idris2_mkBool(                                                              \
      mpz_cmp(((Value_Integer *)(l))->i, ((Value_Integer *)(r))->i) <= 0))
#define lte_Double(l, r) (idris2_cmpop(Double, <=, l, r))
#define lte_Char(l, r) (idris2_cmpop(Char, <=, l, r))
#define lte_string(l, r)                                                       \
  (idris2_mkBool(                                                              \
      strcmp(((Value_String *)(l))->str, ((Value_String *)(r))->str) <= 0))

/* gte */
#define gte_Bits8(l, r) (idris2_cmpop(Bits8, >=, l, r))
#define gte_Bits16(l, r) (idris2_cmpop(Bits16, >=, l, r))
#define gte_Bits32(l, r) (idris2_cmpop(Bits32, >=, l, r))
#define gte_Bits64(l, r) (idris2_cmpop(Bits64, >=, l, r))
#define gte_Int8(l, r) (idris2_cmpop(Int8, >=, l, r))
#define gte_Int16(l, r) (idris2_cmpop(Int16, >=, l, r))
#define gte_Int32(l, r) (idris2_cmpop(Int32, >=, l, r))
#define gte_Int64(l, r) (idris2_cmpop(Int64, >=, l, r))
#define gte_Integer(l, r)                                                      \
  (idris2_mkBool(                                                              \
      mpz_cmp(((Value_Integer *)(l))->i, ((Value_Integer *)(r))->i) >= 0))
#define gte_Double(l, r) (idris2_cmpop(Double, >=, l, r))
#define gte_Char(l, r) (idris2_cmpop(Char, >=, l, r))
#define gte_string(l, r)                                                       \
  (idris2_mkBool(                                                              \
      strcmp(((Value_String *)(l))->str, ((Value_String *)(r))->str) >= 0))
