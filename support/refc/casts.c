#include "casts.h"

#include <inttypes.h>

/*  conversions from Int8  */
Idris2_Value *idris2_cast_Int8_to_Integer(Idris2_Value *input) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_set_si(retVal->i, idris2_vp_to_Int8(input));

  return (Idris2_Value *)retVal;
}

Idris2_Value *idris2_cast_Int8_to_string(Idris2_Value *input) {
  int8_t x = idris2_vp_to_Int8(input);

  int l = snprintf(NULL, 0, "%" PRId8 "", x);
  Idris2_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%" PRId8 "", x);

  return (Idris2_Value *)retVal;
}

/*  conversions from Int16  */
Idris2_Value *idris2_cast_Int16_to_Integer(Idris2_Value *input) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_set_si(retVal->i, idris2_vp_to_Int16(input));

  return (Idris2_Value *)retVal;
}

Idris2_Value *idris2_cast_Int16_to_string(Idris2_Value *input) {
  int16_t x = idris2_vp_to_Int16(input);

  int l = snprintf(NULL, 0, "%" PRId16 "", x);
  Idris2_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%" PRId16 "", x);

  return (Idris2_Value *)retVal;
}

/*  conversions from Int32  */
Idris2_Value *idris2_cast_Int32_to_Integer(Idris2_Value *input) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_set_si(retVal->i, idris2_vp_to_Int32(input));

  return (Idris2_Value *)retVal;
}

Idris2_Value *idris2_cast_Int32_to_string(Idris2_Value *input) {
  int32_t x = idris2_vp_to_Int32(input);

  int l = snprintf(NULL, 0, "%" PRId32 "", x);
  Idris2_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%" PRId32 "", x);

  return (Idris2_Value *)retVal;
}

/*  conversions from Int64  */
Idris2_Value *idris2_cast_Int64_to_Integer(Idris2_Value *input) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_set_si(retVal->i, idris2_vp_to_Int64(input));

  return (Idris2_Value *)retVal;
}

Idris2_Value *idris2_cast_Int64_to_string(Idris2_Value *input) {
  int64_t from = idris2_vp_to_Int64(input);
  int l = snprintf(NULL, 0, "%" PRId64 "", from);
  Idris2_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%" PRId64 "", from);

  return (Idris2_Value *)retVal;
}

Idris2_Value *idris2_cast_Double_to_Integer(Idris2_Value *input) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_set_d(retVal->i, idris2_vp_to_Double(input));

  return (Idris2_Value *)retVal;
}

Idris2_Value *idris2_cast_Double_to_string(Idris2_Value *input) {
  double x = idris2_vp_to_Double(input);

  int l = snprintf(NULL, 0, "%f", x);
  Idris2_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%f", x);

  return (Idris2_Value *)retVal;
}

Idris2_Value *idris2_cast_Char_to_Integer(Idris2_Value *input) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_set_si(retVal->i, idris2_vp_to_Char(input));

  return (Idris2_Value *)retVal;
}

Idris2_Value *idris2_cast_Char_to_string(Idris2_Value *input) {
  Idris2_String *retVal = idris2_mkEmptyString(2);
  retVal->str[0] = idris2_vp_to_Char(input);

  return (Idris2_Value *)retVal;
}

Idris2_Value *idris2_cast_String_to_Bits8(Idris2_Value *input) {
  Idris2_String *from = (Idris2_String *)input;
  return (Idris2_Value *)idris2_mkBits8((uint8_t)atoi(from->str));
}

Idris2_Value *idris2_cast_String_to_Bits16(Idris2_Value *input) {
  Idris2_String *from = (Idris2_String *)input;
  return (Idris2_Value *)idris2_mkBits16((uint16_t)atoi(from->str));
}

Idris2_Value *idris2_cast_String_to_Bits32(Idris2_Value *input) {
  Idris2_String *from = (Idris2_String *)input;
  return (Idris2_Value *)idris2_mkBits32((uint32_t)atoi(from->str));
}

Idris2_Value *idris2_cast_String_to_Bits64(Idris2_Value *input) {
  Idris2_String *from = (Idris2_String *)input;
  return (Idris2_Value *)idris2_mkBits64((uint64_t)atoi(from->str));
}

Idris2_Value *idris2_cast_String_to_Int8(Idris2_Value *input) {
  Idris2_String *from = (Idris2_String *)input;
  return (Idris2_Value *)idris2_mkInt8((int8_t)atoi(from->str));
}

Idris2_Value *idris2_cast_String_to_Int16(Idris2_Value *input) {
  Idris2_String *from = (Idris2_String *)input;
  return (Idris2_Value *)idris2_mkInt16((int16_t)atoi(from->str));
}

Idris2_Value *idris2_cast_String_to_Int32(Idris2_Value *input) {
  Idris2_String *from = (Idris2_String *)input;
  return (Idris2_Value *)idris2_mkInt32((int32_t)atoi(from->str));
}

Idris2_Value *idris2_cast_String_to_Int64(Idris2_Value *input) {
  Idris2_String *from = (Idris2_String *)input;
  return (Idris2_Value *)idris2_mkInt64((int64_t)atoi(from->str));
}

Idris2_Value *idris2_cast_String_to_Integer(Idris2_Value *input) {
  Idris2_String *from = (Idris2_String *)input;

  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_set_str(retVal->i, from->str, 10);

  return (Idris2_Value *)retVal;
}

Idris2_Value *idris2_cast_String_to_Double(Idris2_Value *input) {
  return (Idris2_Value *)idris2_mkDouble(atof(((Idris2_String *)input)->str));
}

/*  conversions from Bits8  */
Idris2_Value *idris2_cast_Bits8_to_Integer(Idris2_Value *input) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_set_ui(retVal->i, idris2_vp_to_Bits8(input));

  return (Idris2_Value *)retVal;
}

Idris2_Value *idris2_cast_Bits8_to_string(Idris2_Value *input) {
  uint8_t x = idris2_vp_to_Bits8(input);

  int l = snprintf(NULL, 0, "%" PRIu8 "", x);
  Idris2_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%" PRIu8 "", x);

  return (Idris2_Value *)retVal;
}

/*  conversions from Bits16  */
Idris2_Value *idris2_cast_Bits16_to_Integer(Idris2_Value *input) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_set_ui(retVal->i, idris2_vp_to_Bits16(input));

  return (Idris2_Value *)retVal;
}

Idris2_Value *idris2_cast_Bits16_to_string(Idris2_Value *input) {
  uint16_t x = idris2_vp_to_Bits16(input);

  int l = snprintf(NULL, 0, "%" PRIu16 "", x);
  Idris2_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%" PRIu16 "", x);

  return (Idris2_Value *)retVal;
}

/*  conversions from Bits32  */
Idris2_Value *idris2_cast_Bits32_to_Integer(Idris2_Value *input) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_set_ui(retVal->i, idris2_vp_to_Bits32(input));

  return (Idris2_Value *)retVal;
}

Idris2_Value *idris2_cast_Bits32_to_string(Idris2_Value *input) {
  uint32_t x = idris2_vp_to_Bits32(input);

  int l = snprintf(NULL, 0, "%" PRIu32 "", x);
  Idris2_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%" PRIu32 "", x);

  return (Idris2_Value *)retVal;
}

/*  conversions from Bits64  */
Idris2_Value *idris2_cast_Bits64_to_Integer(Idris2_Value *input) {
  Idris2_Integer *retVal = idris2_mkInteger();
  mpz_set_ui(retVal->i, idris2_vp_to_Bits64(input));

  return (Idris2_Value *)retVal;
}

Idris2_Value *idris2_cast_Bits64_to_string(Idris2_Value *input) {
  uint64_t x = idris2_vp_to_Bits64(input);

  int l = snprintf(NULL, 0, "%" PRIu64 "", x);
  Idris2_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%" PRIu64 "", x);

  return (Idris2_Value *)retVal;
}

/*  conversions from Integer */
uint64_t mpz_get_lsb(mpz_t i, mp_bitcnt_t b) {
  mpz_t r;
  mpz_init(r);
  mpz_fdiv_r_2exp(r, i, b);
  uint64_t retVal = mpz_get_ui(r);
  mpz_clear(r);
  return retVal;
}

Idris2_Value *idris2_cast_Integer_to_Bits8(Idris2_Value *input) {
  Idris2_Integer *from = (Idris2_Integer *)input;
  return (Idris2_Value *)idris2_mkBits8((uint8_t)mpz_get_lsb(from->i, 8));
}

Idris2_Value *idris2_cast_Integer_to_Bits16(Idris2_Value *input) {
  Idris2_Integer *from = (Idris2_Integer *)input;
  return (Idris2_Value *)idris2_mkBits16((uint16_t)mpz_get_lsb(from->i, 16));
}

Idris2_Value *idris2_cast_Integer_to_Bits32(Idris2_Value *input) {
  Idris2_Integer *from = (Idris2_Integer *)input;
  return (Idris2_Value *)idris2_mkBits32((uint32_t)mpz_get_lsb(from->i, 32));
}

Idris2_Value *idris2_cast_Integer_to_Bits64(Idris2_Value *input) {
  Idris2_Integer *from = (Idris2_Integer *)input;
  return (Idris2_Value *)idris2_mkBits64((uint64_t)mpz_get_lsb(from->i, 64));
}

Idris2_Value *idris2_cast_Integer_to_Int8(Idris2_Value *input) {
  Idris2_Integer *from = (Idris2_Integer *)input;
  return (Idris2_Value *)idris2_mkInt8((int8_t)mpz_get_lsb(from->i, 8));
}

Idris2_Value *idris2_cast_Integer_to_Int16(Idris2_Value *input) {
  Idris2_Integer *from = (Idris2_Integer *)input;
  return (Idris2_Value *)idris2_mkInt16((int16_t)mpz_get_lsb(from->i, 16));
}

Idris2_Value *idris2_cast_Integer_to_Int32(Idris2_Value *input) {
  Idris2_Integer *from = (Idris2_Integer *)input;
  return (Idris2_Value *)idris2_mkInt32((int32_t)mpz_get_lsb(from->i, 32));
}

Idris2_Value *idris2_cast_Integer_to_Int64(Idris2_Value *input) {
  Idris2_Integer *from = (Idris2_Integer *)input;
  return (Idris2_Value *)idris2_mkInt64((int64_t)mpz_get_lsb(from->i, 64));
}

Idris2_Value *idris2_cast_Integer_to_Double(Idris2_Value *input) {
  Idris2_Integer *from = (Idris2_Integer *)input;
  return (Idris2_Value *)idris2_mkDouble(mpz_get_d(from->i));
}

Idris2_Value *idris2_cast_Integer_to_Char(Idris2_Value *input) {
  Idris2_Integer *from = (Idris2_Integer *)input;
  return (Idris2_Value *)idris2_mkChar((unsigned char)mpz_get_lsb(from->i, 8));
}

Idris2_Value *idris2_cast_Integer_to_string(Idris2_Value *input) {
  Idris2_Integer *from = (Idris2_Integer *)input;

  Idris2_String *retVal = IDRIS2_NEW_VALUE(Idris2_String);
  retVal->header.tag = STRING_TAG;
  retVal->str = mpz_get_str(NULL, 10, from->i);

  return (Idris2_Value *)retVal;
}
