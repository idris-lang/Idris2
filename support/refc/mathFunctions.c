#include "mathFunctions.h"
#include "memoryManagement.h"
#include "runtime.h"

/* add */
Idris2_Value *idris2_add_Integer(Idris2_Value *x, Idris2_Value *y) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_add(retVal->i, ((Idris2_Integer *)x)->i, ((Idris2_Integer *)y)->i);
  return (Idris2_Value *)retVal;
}

/* sub */
Idris2_Value *idris2_sub_Integer(Idris2_Value *x, Idris2_Value *y) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_sub(retVal->i, ((Idris2_Integer *)x)->i, ((Idris2_Integer *)y)->i);
  return (Idris2_Value *)retVal;
}

/* negate */
Idris2_Value *idris2_negate_Integer(Idris2_Value *x) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_neg(retVal->i, ((Idris2_Integer *)x)->i);
  return (Idris2_Value *)retVal;
}

/* mul */
Idris2_Value *idris2_mul_Integer(Idris2_Value *x, Idris2_Value *y) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_mul(retVal->i, ((Idris2_Integer *)x)->i, ((Idris2_Integer *)y)->i);
  return (Idris2_Value *)retVal;
}

/* div */
Idris2_Value *idris2_div_Int8(Idris2_Value *x, Idris2_Value *y) {
  // Correction term added to convert from truncated division (C default) to
  // Euclidean division For proof of correctness, see Division and Modulus for
  // Computer Scientists (Daan Leijen)
  // https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

  int8_t num = idris2_vp_to_Int8(x);
  int8_t denom = idris2_vp_to_Int8(y);
  int8_t rem = num % denom;
  return idris2_mkInt8(num / denom + ((rem < 0) ? (denom < 0) ? 1 : -1 : 0));
}
Idris2_Value *idris2_div_Int16(Idris2_Value *x, Idris2_Value *y) {
  // Correction term added to convert from truncated division (C default) to
  // Euclidean division For proof of correctness, see Division and Modulus for
  // Computer Scientists (Daan Leijen)
  // https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

  int16_t num = idris2_vp_to_Int16(x);
  int16_t denom = idris2_vp_to_Int16(y);
  int16_t rem = num % denom;
  return idris2_mkInt16(num / denom + ((rem < 0) ? (denom < 0) ? 1 : -1 : 0));
}
Idris2_Value *idris2_div_Int32(Idris2_Value *x, Idris2_Value *y) {
  // Correction term added to convert from truncated division (C default) to
  // Euclidean division For proof of correctness, see Division and Modulus for
  // Computer Scientists (Daan Leijen)
  // https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

  int32_t num = idris2_vp_to_Int32(x);
  int32_t denom = idris2_vp_to_Int32(y);
  int32_t rem = num % denom;
  return idris2_mkInt32(num / denom + ((rem < 0) ? (denom < 0) ? 1 : -1 : 0));
}
Idris2_Value *idris2_div_Int64(Idris2_Value *x, Idris2_Value *y) {
  // Correction term added to convert from truncated division (C default) to
  // Euclidean division For proof of correctness, see Division and Modulus for
  // Computer Scientists (Daan Leijen)
  // https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

  int64_t num = idris2_vp_to_Int64(x);
  int64_t denom = idris2_vp_to_Int64(y);
  int64_t rem = num % denom;
  return (Idris2_Value *)idris2_mkInt64(num / denom +
                                        ((rem < 0) ? (denom < 0) ? 1 : -1 : 0));
}

Idris2_Value *idris2_div_Integer(Idris2_Value *x, Idris2_Value *y) {
  mpz_t rem, yq;
  mpz_inits(rem, yq, NULL);

  mpz_mod(rem, ((Idris2_Integer *)x)->i, ((Idris2_Integer *)y)->i);
  mpz_sub(yq, ((Idris2_Integer *)x)->i, rem);

  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_divexact(retVal->i, yq, ((Idris2_Integer *)y)->i);

  mpz_clears(rem, yq, NULL);

  return (Idris2_Value *)retVal;
}

/* mod */
Idris2_Value *idris2_mod_Int8(Idris2_Value *x, Idris2_Value *y) {
  int8_t num = idris2_vp_to_Int8(x);
  int8_t denom = idris2_vp_to_Int8(y);
  denom = (denom < 0) ? -denom : denom;
  return (Idris2_Value *)idris2_mkInt8(num % denom + (num < 0 ? denom : 0));
}

Idris2_Value *idris2_mod_Int16(Idris2_Value *x, Idris2_Value *y) {
  int16_t num = idris2_vp_to_Int16(x);
  int16_t denom = idris2_vp_to_Int16(y);
  denom = (denom < 0) ? -denom : denom;
  return (Idris2_Value *)idris2_mkInt16(num % denom + (num < 0 ? denom : 0));
}
Idris2_Value *idris2_mod_Int32(Idris2_Value *x, Idris2_Value *y) {
  int32_t num = idris2_vp_to_Int32(x);
  int32_t denom = idris2_vp_to_Int32(y);
  denom = (denom < 0) ? -denom : denom;
  return (Idris2_Value *)idris2_mkInt32(num % denom + (num < 0 ? denom : 0));
}
Idris2_Value *idris2_mod_Int64(Idris2_Value *x, Idris2_Value *y) {
  int64_t num = idris2_vp_to_Int64(x);
  int64_t denom = idris2_vp_to_Int64(y);
  denom = (denom < 0) ? -denom : denom;
  return (Idris2_Value *)idris2_mkInt64(num % denom + (num < 0 ? denom : 0));
}
Idris2_Value *idris2_mod_Integer(Idris2_Value *x, Idris2_Value *y) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_mod(retVal->i, ((Idris2_Integer *)x)->i, ((Idris2_Integer *)y)->i);
  return (Idris2_Value *)retVal;
}

/* shiftl */
Idris2_Value *idris2_shiftl_Integer(Idris2_Value *x, Idris2_Value *y) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mp_bitcnt_t cnt = (mp_bitcnt_t)mpz_get_ui(((Idris2_Integer *)y)->i);
  mpz_mul_2exp(retVal->i, ((Idris2_Integer *)x)->i, cnt);
  return (Idris2_Value *)retVal;
}

/* shiftr */
Idris2_Value *idris2_shiftr_Integer(Idris2_Value *x, Idris2_Value *y) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mp_bitcnt_t cnt = (mp_bitcnt_t)mpz_get_ui(((Idris2_Integer *)y)->i);
  mpz_fdiv_q_2exp(retVal->i, ((Idris2_Integer *)x)->i, cnt);
  return (Idris2_Value *)retVal;
}

/* and */
Idris2_Value *idris2_and_Integer(Idris2_Value *x, Idris2_Value *y) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_and(retVal->i, ((Idris2_Integer *)x)->i, ((Idris2_Integer *)y)->i);
  return (Idris2_Value *)retVal;
}

/* or */
Idris2_Value *idris2_or_Integer(Idris2_Value *x, Idris2_Value *y) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_ior(retVal->i, ((Idris2_Integer *)x)->i, ((Idris2_Integer *)y)->i);
  return (Idris2_Value *)retVal;
}

/* xor */
Idris2_Value *idris2_xor_Integer(Idris2_Value *x, Idris2_Value *y) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_xor(retVal->i, ((Idris2_Integer *)x)->i, ((Idris2_Integer *)y)->i);
  return (Idris2_Value *)retVal;
}
