#pragma once

#include "cBackend.h"
#include <gmp.h>
#include <stdio.h>

#define idris2_cast_Int8_to_Bits8(x) (x)
#define idris2_cast_Int8_to_Bits16(x) (x)
#define idris2_cast_Int8_to_Bits32(x) (x)
#define idris2_cast_Int8_to_Bits64(x)                                          \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Int8(x)))
#define idris2_cast_Int8_to_Int16(x)                                           \
  (idris2_mkInt16((int16_t)idris2_vp_to_Int8(x)))
#define idris2_cast_Int8_to_Int32(x)                                           \
  (idris2_mkInt32((int32_t)idris2_vp_to_Int8(x)))
#define idris2_cast_Int8_to_Int64(x)                                           \
  (idris2_mkInt64((int64_t)idris2_vp_to_Int8(x)))
Idris2_Value *idris2_cast_Int8_to_Integer(Idris2_Value *);
#define idris2_cast_Int8_to_Double(x)                                          \
  (idris2_mkDouble((double)idris2_vp_to_Int8(x)))
#define idris2_cast_Int8_to_Char(x)                                            \
  (idris2_mkChar((unsigned char)idris2_vp_to_Int8(x)))
Idris2_Value *idris2_cast_Int8_to_string(Idris2_Value *);

#define idris2_cast_Int16_to_Bits8(x)                                          \
  (idris2_mkBits8((uint8_t)idris2_vp_to_Int16(x)))
#define idris2_cast_Int16_to_Bits16(x) (x)
#define idris2_cast_Int16_to_Bits32(x) (x)
#define idris2_cast_Int16_to_Bits64(x)                                         \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Int16(x)))
#define idris2_cast_Int16_to_Int8(x)                                           \
  (idris2_mkInt8((int8_t)idris2_vp_to_Int16(x)))
#define idris2_cast_Int16_to_Int32(x) (x)
#define idris2_cast_Int16_to_Int64(x)                                          \
  (idris2_mkInt64((int64_t)idris2_vp_to_Int16(x)))
Idris2_Value *idris2_cast_Int16_to_Integer(Idris2_Value *);
#define idris2_cast_Int16_to_Double(x)                                         \
  (idris2_mkDouble((double)idris2_vp_to_Int16(x)))
#define idris2_cast_Int16_to_Char(x)                                           \
  (idris2_mkChar((unsigned char)idris2_vp_to_Int16(x)))
Idris2_Value *idris2_cast_Int16_to_string(Idris2_Value *);

#define idris2_cast_Int32_to_Bits8(x)                                          \
  (idris2_mkBits8((uint8_t)idris2_vp_to_Int32(x)))
#define idris2_cast_Int32_to_Bits16(x)                                         \
  (idris2_mkBits16((uint16_t)idris2_vp_to_Int32(x)))
#define idris2_cast_Int32_to_Bits32(x) (x)
#define idris2_cast_Int32_to_Bits64(x)                                         \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Int32(x)))
#define idris2_cast_Int32_to_Int8(x)                                           \
  (idris2_mkInt8((int8_t)idris2_vp_to_Int32(x)))
#define idris2_cast_Int32_to_Int16(x)                                          \
  (idris2_mkInt16((int16_t)idris2_vp_to_Int32(x)))
#define idris2_cast_Int32_to_Int64(x)                                          \
  (idris2_mkInt64((int64_t)idris2_vp_to_Int32(x)))
Idris2_Value *idris2_cast_Int32_to_Integer(Idris2_Value *);
#define idris2_cast_Int32_to_Double(x)                                         \
  (idris2_mkDouble((double)idris2_vp_to_Int32(x)))
#define idris2_cast_Int32_to_Char(x)                                           \
  (idris2_mkChar((unsigned char)idris2_vp_to_Int32(x)))
Idris2_Value *idris2_cast_Int32_to_string(Idris2_Value *);

#define idris2_cast_Int64_to_Bits8(x)                                          \
  (idris2_mkBits8((uint8_t)idris2_vp_to_Int64(x)))
#define idris2_cast_Int64_to_Bits16(x)                                         \
  (idris2_mkBits16((uint16_t)idris2_vp_to_Int64(x)))
#define idris2_cast_Int64_to_Bits32(x)                                         \
  (idris2_mkBits32((uint32_t)idris2_vp_to_Int64(x)))
#define idris2_cast_Int64_to_Bits64(x)                                         \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Int64(x)))
#define idris2_cast_Int64_to_Int8(x)                                           \
  (idris2_mkInt8((int8_t)idris2_vp_to_Int64(x)))
#define idris2_cast_Int64_to_Int16(x)                                          \
  (idris2_mkInt16((int16_t)idris2_vp_to_Int64(x)))
#define idris2_cast_Int64_to_Int32(x)                                          \
  (idris2_mkInt32((int32_t)idris2_vp_to_Int64(x)))
#define idris2_cast_Int64_to_Int64(x) (idris2_newReference(x))
Idris2_Value *idris2_cast_Int64_to_Integer(Idris2_Value *);
#define idris2_cast_Int64_to_Double(x)                                         \
  (idris2_mkDouble((double)idris2_vp_to_Int64(x)))
#define idris2_cast_Int64_to_Char(x)                                           \
  (idris2_mkChar((unsigned char)idris2_vp_to_Int64(x)))
Idris2_Value *idris2_cast_Int64_to_string(Idris2_Value *);

#define idris2_cast_Double_to_Bits8(x)                                         \
  (idris2_mkBits8((uint8_t)idris2_vp_to_Double(x)))
#define idris2_cast_Double_to_Bits16(x)                                        \
  (idris2_mkBits16((uint16_t)idris2_vp_to_Double(x)))
#define idris2_cast_Double_to_Bits32(x)                                        \
  (idris2_mkBits32((uint32_t)idris2_vp_to_Double(x)))
#define idris2_cast_Double_to_Bits64(x)                                        \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Double(x)))
#define idris2_cast_Double_to_Int(x)                                           \
  (idris2_mkInt8((int8_t)idris2_vp_to_Double(x)))
#define idris2_cast_Double_to_Int16(x)                                         \
  (idris2_mkInt16((int16_t)idris2_vp_to_Double(x)))
#define idris2_cast_Double_to_Int32(x)                                         \
  (idris2_mkInt32((int32_t)idris2_vp_to_Double(x)))
#define idris2_cast_Double_to_Int64(x)                                         \
  (idris2_mkInt64((int64_t)idris2_vp_to_Double(x)))
Idris2_Value *idris2_cast_Double_to_Integer(Idris2_Value *);
#define idris2_cast_Double_to_Char(x)                                          \
  (idris2_mkChar((unsigned char)idris2_vp_to_Double))
Idris2_Value *idris2_cast_Double_to_string(Idris2_Value *);

#define idris2_cast_Char_to_Bits8(x)                                           \
  (idris2_mkBits8((uint8_t)idris2_vp_to_Char(x)))
#define idris2_cast_Char_to_Bits16(x)                                          \
  (idris2_mkBits16((uint16_t)idris2_vp_to_Char(x)))
#define idris2_cast_Char_to_Bits32(x)                                          \
  (idris2_mkBits32((uint32_t)idris2_vp_to_Char(x)))
#define idris2_cast_Char_to_Bits64(x)                                          \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Char(x)))
#define idris2_cast_Char_to_Int8(x)                                            \
  (idris2_mkInt8((int8_t)idris2_vp_to_Char(x)))
#define idris2_cast_Char_to_Int16(x)                                           \
  (idris2_mkInt16((int16_t)idris2_vp_to_Char(x)))
#define idris2_cast_Char_to_Int32(x)                                           \
  (idris2_mkInt32((int32_t)idris2_vp_to_Char(x)))
#define idris2_cast_Char_to_Int64(x)                                           \
  (idris2_mkInt64((int64_t)idris2_vp_to_Char(x)))
Idris2_Value *idris2_cast_Char_to_Integer(Idris2_Value *);
#define idris2_cast_Char_to_Double(x)                                          \
  (idris2_mkDouble((double)idris2_vp_to_Char(x)))
Idris2_Value *idris2_cast_Char_to_string(Idris2_Value *);

Idris2_Value *idris2_cast_String_to_Bits8(Idris2_Value *);
Idris2_Value *idris2_cast_String_to_Bits16(Idris2_Value *);
Idris2_Value *idris2_cast_String_to_Bits32(Idris2_Value *);
Idris2_Value *idris2_cast_String_to_Bits64(Idris2_Value *);
Idris2_Value *idris2_cast_String_to_Int8(Idris2_Value *);
Idris2_Value *idris2_cast_String_to_Int16(Idris2_Value *);
Idris2_Value *idris2_cast_String_to_Int32(Idris2_Value *);
Idris2_Value *idris2_cast_String_to_Int64(Idris2_Value *);
Idris2_Value *idris2_cast_String_to_Integer(Idris2_Value *);
Idris2_Value *idris2_cast_String_to_Double(Idris2_Value *);
#define idris2_cast_String_to_Char(x)                                          \
  (idris2_mkChar(((Idris2_String *)(x))->str[0]))

#define idris2_cast_Bits8_to_Bits16(x) (x)
#define idris2_cast_Bits8_to_Bits32(x) (x)
#define idris2_cast_Bits8_to_Bits64(x)                                         \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Bits8(x)))
#define idris2_cast_Bits8_to_Int8(x) (x)
#define idris2_cast_Bits8_to_Int16(x) (x)
#define idris2_cast_Bits8_to_Int32(x) (x)
#define idris2_cast_Bits8_to_Int64(x)                                          \
  (idris2_mkInt64((int64_t)idris2_vp_to_Bits8(x)))
Idris2_Value *idris2_cast_Bits8_to_Integer(Idris2_Value *input);
#define idris2_cast_Bits8_to_Double(x)                                         \
  (idris2_mkDouble((double)idris2_vp_to_Bits8(x)))
#define idris2_cast_Bits8_to_Char(x)                                           \
  (idris2_mkChar((unsigned char)idris2_vp_to_Bits8(x)))
Idris2_Value *idris2_cast_Bits8_to_string(Idris2_Value *input);

#define idris2_cast_Bits16_to_Bits8(x)                                         \
  (idris2_mkBits8((uint8_t)idris2_vp_to_Bits16(x)))
#define idris2_cast_Bits16_to_Bits32(x)                                        \
  (idris2_mkBits32((uint32_t)idris2_vp_to_Bits16(x)))
#define idris2_cast_Bits16_to_Bits64(x)                                        \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Bits16(x)))
#define idris2_cast_Bits16_to_Int8(x)                                          \
  (idris2_mkInt8((int8_t)idris2_vp_to_Bits16(x)))
#define idris2_cast_Bits16_to_Int16(x)                                         \
  (idris2_mkInt16((int16_t)idris2_vp_to_Bits16(x)))
#define idris2_cast_Bits16_to_Int32(x)                                         \
  (idris2_mkInt32((int32_t)idris2_vp_to_Bits16(x)))
#define idris2_cast_Bits16_to_Int64(x)                                         \
  (idris2_mkInt64((int64_t)idris2_vp_to_Bits16(x)))
Idris2_Value *idris2_cast_Bits16_to_Integer(Idris2_Value *input);
#define idris2_cast_Bits16_to_Double(x)                                        \
  (idris2_mkDouble((double)idris2_vp_to_Bits16(x)))
#define idris2_cast_Bits16_to_Char(x)                                          \
  (idris2_mkChar((unsigned char)idris2_vp_to_Bits16(x)))
Idris2_Value *idris2_cast_Bits16_to_string(Idris2_Value *input);

#define idris2_cast_Bits32_to_Bits8(x)                                         \
  (idris2_mkBits8((uint8_t)idris2_vp_to_Bits32(x)))
#define idris2_cast_Bits32_to_Bits16(x)                                        \
  (idris2_mkBits16((uint16_t)idris2_vp_to_Bits32(x)))
#define idris2_cast_Bits32_to_Bits64(x)                                        \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Bits32(x)))
#define idris2_cast_Bits32_to_Int8(x)                                          \
  (idris2_mkBits8((int8_t)idris2_vp_to_Bits32(x)))
#define idris2_cast_Bits32_to_Int16(x)                                         \
  (idris2_mkBits16((int16_t)idris2_vp_to_Bits32(x)))
#define idris2_cast_Bits32_to_Int32(x)                                         \
  (idris2_mkBits32((int32_t)idris2_vp_to_Bits32(x)))
#define idris2_cast_Bits32_to_Int64(x)                                         \
  (idris2_mkBits64((int64_t)idris2_vp_to_Bits32(x)))
Idris2_Value *idris2_cast_Bits32_to_Integer(Idris2_Value *input);
#define idris2_cast_Bits32_to_Double(x)                                        \
  (idris2_mkDouble((double)idris2_vp_to_Bits32(x)))
#define idris2_cast_Bits32_to_Char(x)                                          \
  (idris2_mkChar((unsigned char)idris2_vp_to_Bits32(x)))
Idris2_Value *idris2_cast_Bits32_to_string(Idris2_Value *input);

#define idris2_cast_Bits64_to_Bits8(x)                                         \
  (idris2_mkBits8((uint8_t)idris2_vp_to_Bits64(x)))
#define idris2_cast_Bits64_to_Bits16(x)                                        \
  (idris2_mkBits16((uint16_t)idris2_vp_to_Bits64(x)))
#define idris2_cast_Bits64_to_Bits32(x)                                        \
  (idris2_mkBits32((uint32_t)idris2_vp_to_Bits64(x)))
#define idris2_cast_Bits64_to_Int8(x)                                          \
  (idris2_mkInt8((int8_t)idris2_vp_to_Bits64(x)))
#define idris2_cast_Bits64_to_Int16(x)                                         \
  (idris2_mkInt16((int16_t)idris2_vp_to_Bits64(x)))
#define idris2_cast_Bits64_to_Int32(x)                                         \
  (idris2_mkInt32((int32_t)idris2_vp_to_Bits64(x)))
#define idris2_cast_Bits64_to_Int64(x)                                         \
  (idris2_mkInt64((int64_t)idris2_vp_to_Bits64(x)))
Idris2_Value *idris2_cast_Bits64_to_Integer(Idris2_Value *input);
#define idris2_cast_Bits64_to_Double(x)                                        \
  (idris2_mkDouble((double)idris2_vp_to_Bits64(x)))
#define idris2_cast_Bits64_to_Char(x)                                          \
  (idris2_mkChar((unsigned char)idris2_vp_to_Bits64(x)))
Idris2_Value *idris2_cast_Bits64_to_string(Idris2_Value *input);

Idris2_Value *idris2_cast_Integer_to_Bits8(Idris2_Value *input);
Idris2_Value *idris2_cast_Integer_to_Bits16(Idris2_Value *input);
Idris2_Value *idris2_cast_Integer_to_Bits32(Idris2_Value *input);
Idris2_Value *idris2_cast_Integer_to_Bits64(Idris2_Value *input);
Idris2_Value *idris2_cast_Integer_to_Int8(Idris2_Value *input);
Idris2_Value *idris2_cast_Integer_to_Int16(Idris2_Value *input);
Idris2_Value *idris2_cast_Integer_to_Int32(Idris2_Value *input);
Idris2_Value *idris2_cast_Integer_to_Int64(Idris2_Value *input);
Idris2_Value *idris2_cast_Integer_to_Double(Idris2_Value *input);
Idris2_Value *idris2_cast_Integer_to_Char(Idris2_Value *input);
Idris2_Value *idris2_cast_Integer_to_string(Idris2_Value *input);
