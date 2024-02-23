#include "casts.h"

#include <inttypes.h>

/*  conversions from Int8  */
Value *idris2_cast_Int8_to_Integer(Value *input) {
  Value_Integer *retVal = idris2_mkInteger();
  mpz_set_si(retVal->i, idris2_vp_to_Int8(input));

  return (Value *)retVal;
}

Value *idris2_cast_Int8_to_string(Value *input) {
  int8_t x = idris2_vp_to_Int8(input);

  int l = snprintf(NULL, 0, "%" PRId8 "", x);
  Value_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%" PRId8 "", x);

  return (Value *)retVal;
}

/*  conversions from Int16  */
Value *idris2_cast_Int16_to_Integer(Value *input) {
  Value_Integer *retVal = idris2_mkInteger();
  mpz_set_si(retVal->i, idris2_vp_to_Int16(input));

  return (Value *)retVal;
}

Value *idris2_cast_Int16_to_string(Value *input) {
  int16_t x = idris2_vp_to_Int16(input);

  int l = snprintf(NULL, 0, "%" PRId16 "", x);
  Value_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%" PRId16 "", x);

  return (Value *)retVal;
}

/*  conversions from Int32  */
Value *idris2_cast_Int32_to_Integer(Value *input) {
  Value_Integer *retVal = idris2_mkInteger();
  mpz_set_si(retVal->i, idris2_vp_to_Int32(input));

  return (Value *)retVal;
}

Value *idris2_cast_Int32_to_string(Value *input) {
  int32_t x = idris2_vp_to_Int32(input);

  int l = snprintf(NULL, 0, "%" PRId32 "", x);
  Value_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%" PRId32 "", x);

  return (Value *)retVal;
}

/*  conversions from Int64  */
Value *idris2_cast_Int64_to_Integer(Value *input) {
  Value_Integer *retVal = idris2_mkInteger();
  mpz_set_si(retVal->i, idris2_vp_to_Int64(input));

  return (Value *)retVal;
}

Value *idris2_cast_Int64_to_string(Value *input) {
  int64_t from = idris2_vp_to_Int64(input);
  int l = snprintf(NULL, 0, "%" PRId64 "", from);
  Value_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%" PRId64 "", from);

  return (Value *)retVal;
}

Value *idris2_cast_Double_to_Integer(Value *input) {
  Value_Integer *retVal = idris2_mkInteger();
  mpz_set_d(retVal->i, idris2_vp_to_Double(input));

  return (Value *)retVal;
}

Value *idris2_cast_Double_to_string(Value *input) {
  double x = idris2_vp_to_Double(input);

  int l = snprintf(NULL, 0, "%f", x);
  Value_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%f", x);

  return (Value *)retVal;
}

Value *idris2_cast_Char_to_Integer(Value *input) {
  Value_Integer *retVal = idris2_mkInteger();
  mpz_set_si(retVal->i, idris2_vp_to_Char(input));

  return (Value *)retVal;
}

Value *idris2_cast_Char_to_string(Value *input) {
  Value_String *retVal = idris2_mkEmptyString(2);
  retVal->str[0] = idris2_vp_to_Char(input);

  return (Value *)retVal;
}

Value *idris2_cast_String_to_Bits8(Value *input) {
  Value_String *from = (Value_String *)input;
  return (Value *)idris2_mkBits8((uint8_t)atoi(from->str));
}

Value *idris2_cast_String_to_Bits16(Value *input) {
  Value_String *from = (Value_String *)input;
  return (Value *)idris2_mkBits16((uint16_t)atoi(from->str));
}

Value *idris2_cast_String_to_Bits32(Value *input) {
  Value_String *from = (Value_String *)input;
  return (Value *)idris2_mkBits32((uint32_t)atoi(from->str));
}

Value *idris2_cast_String_to_Bits64(Value *input) {
  Value_String *from = (Value_String *)input;
  return (Value *)idris2_mkBits64((uint64_t)atoi(from->str));
}

Value *idris2_cast_String_to_Int8(Value *input) {
  Value_String *from = (Value_String *)input;
  return (Value *)idris2_mkInt8((int8_t)atoi(from->str));
}

Value *idris2_cast_String_to_Int16(Value *input) {
  Value_String *from = (Value_String *)input;
  return (Value *)idris2_mkInt16((int16_t)atoi(from->str));
}

Value *idris2_cast_String_to_Int32(Value *input) {
  Value_String *from = (Value_String *)input;
  return (Value *)idris2_mkInt32((int32_t)atoi(from->str));
}

Value *idris2_cast_String_to_Int64(Value *input) {
  Value_String *from = (Value_String *)input;
  return (Value *)idris2_mkInt64((int64_t)atoi(from->str));
}

Value *idris2_cast_String_to_Integer(Value *input) {
  Value_String *from = (Value_String *)input;

  Value_Integer *retVal = idris2_mkInteger();
  mpz_set_str(retVal->i, from->str, 10);

  return (Value *)retVal;
}

Value *idris2_cast_String_to_Double(Value *input) {
  return (Value *)idris2_mkDouble(atof(((Value_String *)input)->str));
}

/*  conversions from Bits8  */
Value *idris2_cast_Bits8_to_Integer(Value *input) {
  Value_Integer *retVal = idris2_mkInteger();
  mpz_set_ui(retVal->i, idris2_vp_to_Bits8(input));

  return (Value *)retVal;
}

Value *idris2_cast_Bits8_to_string(Value *input) {
  uint8_t x = idris2_vp_to_Bits8(input);

  int l = snprintf(NULL, 0, "%" PRIu8 "", x);
  Value_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%" PRIu8 "", x);

  return (Value *)retVal;
}

/*  conversions from Bits16  */
Value *idris2_cast_Bits16_to_Integer(Value *input) {
  Value_Integer *retVal = idris2_mkInteger();
  mpz_set_ui(retVal->i, idris2_vp_to_Bits16(input));

  return (Value *)retVal;
}

Value *idris2_cast_Bits16_to_string(Value *input) {
  uint16_t x = idris2_vp_to_Bits16(input);

  int l = snprintf(NULL, 0, "%" PRIu16 "", x);
  Value_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%" PRIu16 "", x);

  return (Value *)retVal;
}

/*  conversions from Bits32  */
Value *idris2_cast_Bits32_to_Integer(Value *input) {
  Value_Integer *retVal = idris2_mkInteger();
  mpz_set_ui(retVal->i, idris2_vp_to_Bits32(input));

  return (Value *)retVal;
}

Value *idris2_cast_Bits32_to_string(Value *input) {
  uint32_t x = idris2_vp_to_Bits32(input);

  int l = snprintf(NULL, 0, "%" PRIu32 "", x);
  Value_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%" PRIu32 "", x);

  return (Value *)retVal;
}

/*  conversions from Bits64  */
Value *idris2_cast_Bits64_to_Integer(Value *input) {
  Value_Integer *retVal = idris2_mkInteger();
  mpz_set_ui(retVal->i, idris2_vp_to_Bits64(input));

  return (Value *)retVal;
}

Value *idris2_cast_Bits64_to_string(Value *input) {
  uint64_t x = idris2_vp_to_Bits64(input);

  int l = snprintf(NULL, 0, "%" PRIu64 "", x);
  Value_String *retVal = idris2_mkEmptyString(l + 1);
  sprintf(retVal->str, "%" PRIu64 "", x);

  return (Value *)retVal;
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

Value *idris2_cast_Integer_to_Bits8(Value *input) {
  Value_Integer *from = (Value_Integer *)input;
  return (Value *)idris2_mkBits8((uint8_t)mpz_get_lsb(from->i, 8));
}

Value *idris2_cast_Integer_to_Bits16(Value *input) {
  Value_Integer *from = (Value_Integer *)input;
  return (Value *)idris2_mkBits16((uint16_t)mpz_get_lsb(from->i, 16));
}

Value *idris2_cast_Integer_to_Bits32(Value *input) {
  Value_Integer *from = (Value_Integer *)input;
  return (Value *)idris2_mkBits32((uint32_t)mpz_get_lsb(from->i, 32));
}

Value *idris2_cast_Integer_to_Bits64(Value *input) {
  Value_Integer *from = (Value_Integer *)input;
  return (Value *)idris2_mkBits64((uint64_t)mpz_get_lsb(from->i, 64));
}

Value *idris2_cast_Integer_to_Int8(Value *input) {
  Value_Integer *from = (Value_Integer *)input;
  return (Value *)idris2_mkInt8((int8_t)mpz_get_lsb(from->i, 8));
}

Value *idris2_cast_Integer_to_Int16(Value *input) {
  Value_Integer *from = (Value_Integer *)input;
  return (Value *)idris2_mkInt16((int16_t)mpz_get_lsb(from->i, 16));
}

Value *idris2_cast_Integer_to_Int32(Value *input) {
  Value_Integer *from = (Value_Integer *)input;
  return (Value *)idris2_mkInt32((int32_t)mpz_get_lsb(from->i, 32));
}

Value *idris2_cast_Integer_to_Int64(Value *input) {
  Value_Integer *from = (Value_Integer *)input;
  return (Value *)idris2_mkInt64((int64_t)mpz_get_lsb(from->i, 64));
}

Value *idris2_cast_Integer_to_Double(Value *input) {
  Value_Integer *from = (Value_Integer *)input;
  return (Value *)idris2_mkDouble(mpz_get_d(from->i));
}

Value *idris2_cast_Integer_to_Char(Value *input) {
  Value_Integer *from = (Value_Integer *)input;
  return (Value *)idris2_mkChar((unsigned char)mpz_get_lsb(from->i, 8));
}

Value *idris2_cast_Integer_to_string(Value *input) {
  Value_Integer *from = (Value_Integer *)input;

  Value_String *retVal = IDRIS2_NEW_VALUE(Value_String);
  retVal->header.tag = STRING_TAG;
  retVal->str = mpz_get_str(NULL, 10, from->i);

  return (Value *)retVal;
}
