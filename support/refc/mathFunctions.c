#include "mathFunctions.h"
#include "memoryManagement.h"
#include "refc_util.h"
#include "runtime.h"
#include <inttypes.h>
#include <stdint.h>

/* add */
Value *idris2_add_Integer(Value *x, Value *y) {
  Value_Integer *retVal = idris2_mkInteger();
#ifndef IDRIS2_NO_GMP
  mpz_add(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
#else
  int64_t xi = ((Value_Integer *)x)->i;
  int64_t yi = ((Value_Integer *)y)->i;
  int64_t result;
#if defined(__GNUC__) || defined(__clang__)
  IDRIS2_REFC_VERIFY(!__builtin_add_overflow(xi, yi, &result),
                     "Integer addition overflow (IDRIS2_NO_GMP): "
                     "%" PRId64 " + %" PRId64,
                     xi, yi);
#else
  /* Portable check: overflow iff both operands share a sign that the
   * result does not. */
  result = xi + yi;
  IDRIS2_REFC_VERIFY(!((xi ^ result) & (yi ^ result) & INT64_MIN),
                     "Integer addition overflow (IDRIS2_NO_GMP)");
#endif
  retVal->i = result;
#endif
  return (Value *)retVal;
}

/* sub */
Value *idris2_sub_Integer(Value *x, Value *y) {
  Value_Integer *retVal = idris2_mkInteger();
#ifndef IDRIS2_NO_GMP
  mpz_sub(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
#else
  int64_t xi = ((Value_Integer *)x)->i;
  int64_t yi = ((Value_Integer *)y)->i;
  int64_t result;
#if defined(__GNUC__) || defined(__clang__)
  IDRIS2_REFC_VERIFY(!__builtin_sub_overflow(xi, yi, &result),
                     "Integer subtraction overflow (IDRIS2_NO_GMP): "
                     "%" PRId64 " - %" PRId64,
                     xi, yi);
#else
  /* Portable check: overflow iff operands differ in sign and the result
   * differs in sign from the minuend. */
  result = xi - yi;
  IDRIS2_REFC_VERIFY(!((xi ^ yi) & (xi ^ result) & INT64_MIN),
                     "Integer subtraction overflow (IDRIS2_NO_GMP)");
#endif
  retVal->i = result;
#endif
  return (Value *)retVal;
}

/* negate */
Value *idris2_negate_Integer(Value *x) {
  Value_Integer *retVal = idris2_mkInteger();
#ifndef IDRIS2_NO_GMP
  mpz_neg(retVal->i, ((Value_Integer *)x)->i);
#else
  int64_t xi = ((Value_Integer *)x)->i;
  /* -INT64_MIN has no representation in int64_t. */
  IDRIS2_REFC_VERIFY(xi != INT64_MIN,
                     "Integer negation overflow (IDRIS2_NO_GMP): INT64_MIN");
  retVal->i = -xi;
#endif
  return (Value *)retVal;
}

/* mul */
Value *idris2_mul_Integer(Value *x, Value *y) {
  Value_Integer *retVal = idris2_mkInteger();
#ifndef IDRIS2_NO_GMP
  mpz_mul(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
#else
  int64_t xi = ((Value_Integer *)x)->i;
  int64_t yi = ((Value_Integer *)y)->i;
  int64_t result;
#if defined(__GNUC__) || defined(__clang__)
  IDRIS2_REFC_VERIFY(!__builtin_mul_overflow(xi, yi, &result),
                     "Integer multiplication overflow (IDRIS2_NO_GMP): "
                     "%" PRId64 " * %" PRId64,
                     xi, yi);
#else
  /* Portable fallback: detect via divide-and-check. */
  result = xi * yi;
  IDRIS2_REFC_VERIFY(xi == 0 || result / xi == yi,
                     "Integer multiplication overflow (IDRIS2_NO_GMP)");
#endif
  retVal->i = result;
#endif
  return (Value *)retVal;
}

/* div */
Value *idris2_div_Int8(Value *x, Value *y) {
  // Correction term added to convert from truncated division (C default) to
  // Euclidean division For proof of correctness, see Division and Modulus for
  // Computer Scientists (Daan Leijen)
  // https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

  int8_t num = idris2_vp_to_Int8(x);
  int8_t denom = idris2_vp_to_Int8(y);
  int8_t rem = num % denom;
  return idris2_mkInt8(num / denom + ((rem < 0) ? (denom < 0) ? 1 : -1 : 0));
}
Value *idris2_div_Int16(Value *x, Value *y) {
  // Correction term added to convert from truncated division (C default) to
  // Euclidean division For proof of correctness, see Division and Modulus for
  // Computer Scientists (Daan Leijen)
  // https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

  int16_t num = idris2_vp_to_Int16(x);
  int16_t denom = idris2_vp_to_Int16(y);
  int16_t rem = num % denom;
  return idris2_mkInt16(num / denom + ((rem < 0) ? (denom < 0) ? 1 : -1 : 0));
}
Value *idris2_div_Int32(Value *x, Value *y) {
  // Correction term added to convert from truncated division (C default) to
  // Euclidean division For proof of correctness, see Division and Modulus for
  // Computer Scientists (Daan Leijen)
  // https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

  int32_t num = idris2_vp_to_Int32(x);
  int32_t denom = idris2_vp_to_Int32(y);
  int32_t rem = num % denom;
  return idris2_mkInt32(num / denom + ((rem < 0) ? (denom < 0) ? 1 : -1 : 0));
}
Value *idris2_div_Int64(Value *x, Value *y) {
  // Correction term added to convert from truncated division (C default) to
  // Euclidean division For proof of correctness, see Division and Modulus for
  // Computer Scientists (Daan Leijen)
  // https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

  int64_t num = idris2_vp_to_Int64(x);
  int64_t denom = idris2_vp_to_Int64(y);
  int64_t rem = num % denom;
  return (Value *)idris2_mkInt64(num / denom +
                                 ((rem < 0) ? (denom < 0) ? 1 : -1 : 0));
}

Value *idris2_div_Integer(Value *x, Value *y) {
  Value_Integer *retVal = idris2_mkInteger();
#ifndef IDRIS2_NO_GMP
  mpz_t rem, yq;
  mpz_inits(rem, yq, NULL);
  mpz_mod(rem, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
  mpz_sub(yq, ((Value_Integer *)x)->i, rem);
  mpz_divexact(retVal->i, yq, ((Value_Integer *)y)->i);
  mpz_clears(rem, yq, NULL);
#else
  int64_t xi = ((Value_Integer *)x)->i;
  int64_t yi = ((Value_Integer *)y)->i;
  int64_t rem = xi % yi;
  if (rem < 0)
    rem += (yi < 0) ? -yi : yi;
  retVal->i = (xi - rem) / yi;
#endif
  return (Value *)retVal;
}

/* mod */
Value *idris2_mod_Int8(Value *x, Value *y) {
  int8_t num = idris2_vp_to_Int8(x);
  int8_t denom = idris2_vp_to_Int8(y);
  denom = (denom < 0) ? -denom : denom;
  return (Value *)idris2_mkInt8(num % denom + (num < 0 ? denom : 0));
}

Value *idris2_mod_Int16(Value *x, Value *y) {
  int16_t num = idris2_vp_to_Int16(x);
  int16_t denom = idris2_vp_to_Int16(y);
  denom = (denom < 0) ? -denom : denom;
  return (Value *)idris2_mkInt16(num % denom + (num < 0 ? denom : 0));
}
Value *idris2_mod_Int32(Value *x, Value *y) {
  int32_t num = idris2_vp_to_Int32(x);
  int32_t denom = idris2_vp_to_Int32(y);
  denom = (denom < 0) ? -denom : denom;
  return (Value *)idris2_mkInt32(num % denom + (num < 0 ? denom : 0));
}
Value *idris2_mod_Int64(Value *x, Value *y) {
  int64_t num = idris2_vp_to_Int64(x);
  int64_t denom = idris2_vp_to_Int64(y);
  denom = (denom < 0) ? -denom : denom;
  return (Value *)idris2_mkInt64(num % denom + (num < 0 ? denom : 0));
}
Value *idris2_mod_Integer(Value *x, Value *y) {
  Value_Integer *retVal = idris2_mkInteger();
#ifndef IDRIS2_NO_GMP
  mpz_mod(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
#else
  int64_t xi = ((Value_Integer *)x)->i;
  int64_t yi = ((Value_Integer *)y)->i;
  int64_t rem = xi % yi;
  if (rem < 0)
    rem += (yi < 0) ? -yi : yi;
  retVal->i = rem;
#endif
  return (Value *)retVal;
}

/* shiftl */
Value *idris2_shiftl_Integer(Value *x, Value *y) {
  Value_Integer *retVal = idris2_mkInteger();
#ifndef IDRIS2_NO_GMP
  mp_bitcnt_t cnt = (mp_bitcnt_t)mpz_get_ui(((Value_Integer *)y)->i);
  mpz_mul_2exp(retVal->i, ((Value_Integer *)x)->i, cnt);
#else
  int64_t cnt = ((Value_Integer *)y)->i;
  retVal->i = (cnt <= 0 || cnt >= 63) ? 0 : ((Value_Integer *)x)->i << cnt;
#endif
  return (Value *)retVal;
}

/* shiftr */
Value *idris2_shiftr_Integer(Value *x, Value *y) {
  Value_Integer *retVal = idris2_mkInteger();
#ifndef IDRIS2_NO_GMP
  mp_bitcnt_t cnt = (mp_bitcnt_t)mpz_get_ui(((Value_Integer *)y)->i);
  mpz_fdiv_q_2exp(retVal->i, ((Value_Integer *)x)->i, cnt);
#else
  int64_t cnt = ((Value_Integer *)y)->i;
  int64_t xi = ((Value_Integer *)x)->i;
  retVal->i = (cnt <= 0) ? xi : (cnt >= 63) ? (xi < 0 ? -1 : 0) : xi >> cnt;
#endif
  return (Value *)retVal;
}

/* and */
Value *idris2_and_Integer(Value *x, Value *y) {
  Value_Integer *retVal = idris2_mkInteger();
#ifndef IDRIS2_NO_GMP
  mpz_and(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
#else
  retVal->i = ((Value_Integer *)x)->i & ((Value_Integer *)y)->i;
#endif
  return (Value *)retVal;
}

/* or */
Value *idris2_or_Integer(Value *x, Value *y) {
  Value_Integer *retVal = idris2_mkInteger();
#ifndef IDRIS2_NO_GMP
  mpz_ior(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
#else
  retVal->i = ((Value_Integer *)x)->i | ((Value_Integer *)y)->i;
#endif
  return (Value *)retVal;
}

/* xor */
Value *idris2_xor_Integer(Value *x, Value *y) {
  Value_Integer *retVal = idris2_mkInteger();
#ifndef IDRIS2_NO_GMP
  mpz_xor(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
#else
  retVal->i = ((Value_Integer *)x)->i ^ ((Value_Integer *)y)->i;
#endif
  return (Value *)retVal;
}
