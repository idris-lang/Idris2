#pragma once

#include "cBackend.h"
#include <gmp.h>
#include <stdio.h>

#define cast_Int8_to_Bits8(x) (x)
#define cast_Int8_to_Bits16(x) (x)
#define cast_Int8_to_Bits32(x) (x)
#define cast_Int8_to_Bits64(x) (idris2_mkBits64((uint64_t)idris2_vp_to_Int8(x)))
#define cast_Int8_to_Int16(x) (idris2_mkInt16((int16_t)idris2_vp_to_Int8(x)))
#define cast_Int8_to_Int32(x) (idris2_mkInt32((int32_t)idris2_vp_to_Int8(x)))
#define cast_Int8_to_Int64(x) (idris2_mkInt64((int64_t)idris2_vp_to_Int8(x)))
Value *cast_Int8_to_Integer(Value *);
#define cast_Int8_to_Double(x) (idris2_mkDouble((double)idris2_vp_to_Int8(x)))
#define cast_Int8_to_Char(x)                                                   \
  (idris2_mkChar((unsigned char)idris2_vp_to_Int8(x)))
Value *cast_Int8_to_string(Value *);

#define cast_Int16_to_Bits8(x) (idris2_mkBits8((uint8_t)idris2_vp_to_Int16(x)))
#define cast_Int16_to_Bits16(x) (x)
#define cast_Int16_to_Bits32(x) (x)
#define cast_Int16_to_Bits64(x)                                                \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Int16(x)))
#define cast_Int16_to_Int8(x) (idris2_mkInt8((int8_t)idris2_vp_to_Int16(x)))
#define cast_Int16_to_Int32(x) (x)
#define cast_Int16_to_Int64(x) (idris2_mkInt64((int64_t)idris2_vp_to_Int16(x)))
Value *cast_Int16_to_Integer(Value *);
#define cast_Int16_to_Double(x) (idris2_mkDouble((double)idris2_vp_to_Int16(x)))
#define cast_Int16_to_Char(x)                                                  \
  (idris2_mkChar((unsigned char)idris2_vp_to_Int16(x)))
Value *cast_Int16_to_string(Value *);

#define cast_Int32_to_Bits8(x) (idris2_mkBits8((uint8_t)idris2_vp_to_Int32(x)))
#define cast_Int32_to_Bits16(x)                                                \
  (idris2_mkBits16((uint16_t)idris2_vp_to_Int32(x)))
#define cast_Int32_to_Bits32(x) (x)
#define cast_Int32_to_Bits64(x)                                                \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Int32(x)))
#define cast_Int32_to_Int8(x) (idris2_mkInt8((int8_t)idris2_vp_to_Int32(x)))
#define cast_Int32_to_Int16(x) (idris2_mkInt16((int16_t)idris2_vp_to_Int32(x)))
#define cast_Int32_to_Int64(x) (idris2_mkInt64((int64_t)idris2_vp_to_Int32(x)))
Value *cast_Int32_to_Integer(Value *);
#define cast_Int32_to_Double(x) (idris2_mkDouble((double)idris2_vp_to_Int32(x)))
#define cast_Int32_to_Char(x)                                                  \
  (idris2_mkChar((unsigned char)idris2_vp_to_Int32(x)))
Value *cast_Int32_to_string(Value *);

#define cast_Int64_to_Bits8(x) (idris2_mkBits8((uint8_t)idris2_vp_to_Int64(x)))
#define cast_Int64_to_Bits16(x)                                                \
  (idris2_mkBits16((uint16_t)idris2_vp_to_Int64(x)))
#define cast_Int64_to_Bits32(x)                                                \
  (idris2_mkBits32((uint32_t)idris2_vp_to_Int64(x)))
#define cast_Int64_to_Bits64(x)                                                \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Int64(x)))
#define cast_Int64_to_Int8(x) (idris2_mkInt8((int8_t)idris2_vp_to_Int64(x)))
#define cast_Int64_to_Int16(x) (idris2_mkInt16((int16_t)idris2_vp_to_Int64(x)))
#define cast_Int64_to_Int32(x) (idris2_mkInt32((int32_t)idris2_vp_to_Int64(x)))
#define cast_Int64_to_Int64(x) (newReference(x))
Value *cast_Int64_to_Integer(Value *);
#define cast_Int64_to_Double(x) (idris2_mkDouble((double)idris2_vp_to_Int64(x)))
#define cast_Int64_to_Char(x)                                                  \
  (idris2_mkChar((unsigned char)idris2_vp_to_Int64(x)))
Value *cast_Int64_to_string(Value *);

#define cast_Double_to_Bits8(x)                                                \
  (idris2_mkBits8((uint8_t)idris2_vp_to_Double(x)))
#define cast_Double_to_Bits16(x)                                               \
  (idris2_mkBits16((uint16_t)idris2_vp_to_Double(x)))
#define cast_Double_to_Bits32(x)                                               \
  (idris2_mkBits32((uint32_t)idris2_vp_to_Double(x)))
#define cast_Double_to_Bits64(x)                                               \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Double(x)))
#define cast_Double_to_Int(x) (idris2_mkInt8((int8_t)idris2_vp_to_Double(x)))
#define cast_Double_to_Int16(x)                                                \
  (idris2_mkInt16((int16_t)idris2_vp_to_Double(x)))
#define cast_Double_to_Int32(x)                                                \
  (idris2_mkInt32((int32_t)idris2_vp_to_Double(x)))
#define cast_Double_to_Int64(x)                                                \
  (idris2_mkInt64((int64_t)idris2_vp_to_Double(x)))
Value *cast_Double_to_Integer(Value *);
#define cast_Double_to_Char(x)                                                 \
  (idris2_mkChar((unsigned char)idris2_vp_to_Double))
Value *cast_Double_to_string(Value *);

#define cast_Char_to_Bits8(x) (idris2_mkBits8((uint8_t)idris2_vp_to_Char(x)))
#define cast_Char_to_Bits16(x) (idris2_mkBits16((uint16_t)idris2_vp_to_Char(x)))
#define cast_Char_to_Bits32(x) (idris2_mkBits32((uint32_t)idris2_vp_to_Char(x)))
#define cast_Char_to_Bits64(x) (idris2_mkBits64((uint64_t)idris2_vp_to_Char(x)))
#define cast_Char_to_Int8(x) (idris2_mkInt8((int8_t)idris2_vp_to_Char(x)))
#define cast_Char_to_Int16(x) (idris2_mkInt16((int16_t)idris2_vp_to_Char(x)))
#define cast_Char_to_Int32(x) (idris2_mkInt32((int32_t)idris2_vp_to_Char(x)))
#define cast_Char_to_Int64(x) (idris2_mkInt64((int64_t)idris2_vp_to_Char(x)))
Value *cast_Char_to_Integer(Value *);
#define cast_Char_to_Double(x) (idris2_mkDouble((double)idris2_vp_to_Char(x)))
Value *cast_Char_to_string(Value *);

Value *cast_string_to_Bits8(Value *);
Value *cast_string_to_Bits16(Value *);
Value *cast_string_to_Bits32(Value *);
Value *cast_string_to_Bits64(Value *);
Value *cast_string_to_Int8(Value *);
Value *cast_string_to_Int16(Value *);
Value *cast_string_to_Int32(Value *);
Value *cast_string_to_Int64(Value *);
Value *cast_string_to_Integer(Value *);
Value *cast_string_to_Double(Value *);
#define cast_string_to_Char(x) (idris2_mkChar(((Value_String *)(x))->str[0]))

#define cast_Bits8_to_Bits16(x) (x)
#define cast_Bits8_to_Bits32(x) (x)
#define cast_Bits8_to_Bits64(x)                                                \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Bits8(x)))
#define cast_Bits8_to_Int8(x) (x)
#define cast_Bits8_to_Int16(x) (x)
#define cast_Bits8_to_Int32(x) (x)
#define cast_Bits8_to_Int64(x) (idris2_mkInt64((int64_t)idris2_vp_to_Bits8(x)))
Value *cast_Bits8_to_Integer(Value *input);
#define cast_Bits8_to_Double(x) (idris2_mkDouble((double)idris2_vp_to_Bits8(x)))
#define cast_Bits8_to_Char(x)                                                  \
  (idris2_mkChar((unsigned char)idris2_vp_to_Bits8(x)))
Value *cast_Bits8_to_string(Value *input);

#define cast_Bits16_to_Bits8(x)                                                \
  (idris2_mkBits8((uint8_t)idris2_vp_to_Bits16(x)))
#define cast_Bits16_to_Bits32(x)                                               \
  (idris2_mkBits32((uint32_t)idris2_vp_to_Bits16(x)))
#define cast_Bits16_to_Bits64(x)                                               \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Bits16(x)))
#define cast_Bits16_to_Int8(x) (idris2_mkInt8((int8_t)idris2_vp_to_Bits16(x)))
#define cast_Bits16_to_Int16(x)                                                \
  (idris2_mkInt16((int16_t)idris2_vp_to_Bits16(x)))
#define cast_Bits16_to_Int32(x)                                                \
  (idris2_mkInt32((int32_t)idris2_vp_to_Bits16(x)))
#define cast_Bits16_to_Int64(x)                                                \
  (idris2_mkInt64((int64_t)idris2_vp_to_Bits16(x)))
Value *cast_Bits16_to_Integer(Value *input);
#define cast_Bits16_to_Double(x)                                               \
  (idris2_mkDouble((double)idris2_vp_to_Bits16(x)))
#define cast_Bits16_to_Char(x)                                                 \
  (idris2_mkChar((unsigned char)idris2_vp_to_Bits16(x)))
Value *cast_Bits16_to_string(Value *input);

#define cast_Bits32_to_Bits8(x)                                                \
  (idris2_mkBits8((uint8_t)idris2_vp_to_Bits32(x)))
#define cast_Bits32_to_Bits16(x)                                               \
  (idris2_mkBits16((uint16_t)idris2_vp_to_Bits32(x)))
#define cast_Bits32_to_Bits64(x)                                               \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Bits32(x)))
#define cast_Bits32_to_Int8(x) (idris2_mkBits8((int8_t)idris2_vp_to_Bits32(x)))
#define cast_Bits32_to_Int16(x)                                                \
  (idris2_mkBits16((int16_t)idris2_vp_to_Bits32(x)))
#define cast_Bits32_to_Int32(x)                                                \
  (idris2_mkBits32((int32_t)idris2_vp_to_Bits32(x)))
#define cast_Bits32_to_Int64(x)                                                \
  (idris2_mkBits64((int64_t)idris2_vp_to_Bits32(x)))
Value *cast_Bits32_to_Integer(Value *input);
#define cast_Bits32_to_Double(x)                                               \
  (idris2_mkDouble((double)idris2_vp_to_Bits32(x)))
#define cast_Bits32_to_Char(x)                                                 \
  (idris2_mkChar((unsigned char)idris2_vp_to_Bits32(x)))
Value *cast_Bits32_to_string(Value *input);

#define cast_Bits64_to_Bits8(x)                                                \
  (idris2_mkBits8((uint8_t)idris2_vp_to_Bits64(x)))
#define cast_Bits64_to_Bits16(x)                                               \
  (idris2_mkBits16((uint16_t)idris2_vp_to_Bits64(x)))
#define cast_Bits64_to_Bits32(x)                                               \
  (idris2_mkBits32((uint32_t)idris2_vp_to_Bits64(x)))
#define cast_Bits64_to_Int8(x) (idris2_mkInt8((int8_t)idris2_vp_to_Bits64(x)))
#define cast_Bits64_to_Int16(x)                                                \
  (idris2_mkInt16((int16_t)idris2_vp_to_Bits64(x)))
#define cast_Bits64_to_Int32(x)                                                \
  (idris2_mkInt32((int32_t)idris2_vp_to_Bits64(x)))
#define cast_Bits64_to_Int64(x)                                                \
  (idris2_mkInt64((int64_t)idris2_vp_to_Bits64(x)))
Value *cast_Bits64_to_Integer(Value *input);
#define cast_Bits64_to_Double(x)                                               \
  (idris2_mkDouble((double)idris2_vp_to_Bits64(x)))
#define cast_Bits64_to_Char(x)                                                 \
  (idris2_mkChar((unsigned char)idris2_vp_to_Bits64(x)))
Value *cast_Bits64_to_string(Value *input);

Value *cast_Integer_to_Bits8(Value *input);
Value *cast_Integer_to_Bits16(Value *input);
Value *cast_Integer_to_Bits32(Value *input);
Value *cast_Integer_to_Bits64(Value *input);
Value *cast_Integer_to_Int8(Value *input);
Value *cast_Integer_to_Int16(Value *input);
Value *cast_Integer_to_Int32(Value *input);
Value *cast_Integer_to_Int64(Value *input);
Value *cast_Integer_to_Double(Value *input);
Value *cast_Integer_to_Char(Value *input);
Value *cast_Integer_to_string(Value *input);
