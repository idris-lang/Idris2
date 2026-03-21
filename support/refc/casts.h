#pragma once

#include "cBackend.h"
#ifndef IDRIS2_NO_GMP
#  include <gmp.h>
#endif
#include <stdio.h>

/* Valid Unicode codepoint check for cast-to-Char.
 * Returns 0 (null char) for values that are:
 *   - negative (sign-extended to uint32_t → > 0x10FFFF)
 *   - in the surrogate range [0xD800, 0xDFFF]
 *   - above the Unicode maximum 0x10FFFF
 * Otherwise returns the codepoint unchanged. */
static inline uint32_t idris2_validCodePoint(uint32_t cp) {
    if (cp > 0x10FFFFu) return 0u;
    if (cp >= 0xD800u && cp <= 0xDFFFu) return 0u;
    return cp;
}

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
Value *idris2_cast_Int8_to_Integer(Value *);
#define idris2_cast_Int8_to_Double(x)                                          \
  (idris2_mkDouble((double)idris2_vp_to_Int8(x)))
#define idris2_cast_Int8_to_Char(x)                                            \
  (idris2_mkChar(idris2_validCodePoint((uint32_t)(int32_t)idris2_vp_to_Int8(x))))
Value *idris2_cast_Int8_to_String(Value *);

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
Value *idris2_cast_Int16_to_Integer(Value *);
#define idris2_cast_Int16_to_Double(x)                                         \
  (idris2_mkDouble((double)idris2_vp_to_Int16(x)))
#define idris2_cast_Int16_to_Char(x)                                           \
  (idris2_mkChar(idris2_validCodePoint((uint32_t)(int32_t)idris2_vp_to_Int16(x))))
Value *idris2_cast_Int16_to_String(Value *);

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
Value *idris2_cast_Int32_to_Integer(Value *);
#define idris2_cast_Int32_to_Double(x)                                         \
  (idris2_mkDouble((double)idris2_vp_to_Int32(x)))
#define idris2_cast_Int32_to_Char(x)                                           \
  (idris2_mkChar(idris2_validCodePoint((uint32_t)(int32_t)idris2_vp_to_Int32(x))))
Value *idris2_cast_Int32_to_String(Value *);

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
Value *idris2_cast_Int64_to_Integer(Value *);
#define idris2_cast_Int64_to_Double(x)                                         \
  (idris2_mkDouble((double)idris2_vp_to_Int64(x)))
#define idris2_cast_Int64_to_Char(x)                                           \
  (idris2_mkChar(idris2_validCodePoint((uint32_t)(int64_t)idris2_vp_to_Int64(x))))
Value *idris2_cast_Int64_to_String(Value *);

#define idris2_cast_Double_to_Bits8(x)                                         \
  (idris2_mkBits8((uint8_t)idris2_vp_to_Double(x)))
#define idris2_cast_Double_to_Bits16(x)                                        \
  (idris2_mkBits16((uint16_t)idris2_vp_to_Double(x)))
#define idris2_cast_Double_to_Bits32(x)                                        \
  (idris2_mkBits32((uint32_t)idris2_vp_to_Double(x)))
#define idris2_cast_Double_to_Bits64(x)                                        \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Double(x)))
/* For Double → fixed-width signed int: truncate towards 0 via int64_t first
 * so that out-of-range doubles wrap correctly via defined C behaviour. */
#define idris2_cast_Double_to_Int8(x)                                          \
  (idris2_mkInt8((int8_t)(int64_t)idris2_vp_to_Double(x)))
#define idris2_cast_Double_to_Int(x)                                           \
  (idris2_mkInt64((int64_t)idris2_vp_to_Double(x)))
#define idris2_cast_Double_to_Int16(x)                                         \
  (idris2_mkInt16((int16_t)(int64_t)idris2_vp_to_Double(x)))
#define idris2_cast_Double_to_Int32(x)                                         \
  (idris2_mkInt32((int32_t)(int64_t)idris2_vp_to_Double(x)))
#define idris2_cast_Double_to_Int64(x)                                         \
  (idris2_mkInt64((int64_t)idris2_vp_to_Double(x)))
Value *idris2_cast_Double_to_Integer(Value *);
#define idris2_cast_Double_to_Char(x)                                          \
  (idris2_mkChar(idris2_validCodePoint((uint32_t)(int64_t)idris2_vp_to_Double(x))))
Value *idris2_cast_Double_to_String(Value *);

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
Value *idris2_cast_Char_to_Integer(Value *);
#define idris2_cast_Char_to_Double(x)                                          \
  (idris2_mkDouble((double)idris2_vp_to_Char(x)))
Value *idris2_cast_Char_to_String(Value *);

Value *idris2_cast_String_to_Bits8(Value *);
Value *idris2_cast_String_to_Bits16(Value *);
Value *idris2_cast_String_to_Bits32(Value *);
Value *idris2_cast_String_to_Bits64(Value *);
Value *idris2_cast_String_to_Int8(Value *);
Value *idris2_cast_String_to_Int16(Value *);
Value *idris2_cast_String_to_Int32(Value *);
Value *idris2_cast_String_to_Int64(Value *);
Value *idris2_cast_String_to_Integer(Value *);
Value *idris2_cast_String_to_Double(Value *);
#define idris2_cast_String_to_Char(x)                                          \
  (idris2_cast_String_to_Char_impl(x))
Value *idris2_cast_String_to_Char_impl(Value *s);

#define idris2_cast_Bits8_to_Bits16(x) (x)
#define idris2_cast_Bits8_to_Bits32(x) (x)
#define idris2_cast_Bits8_to_Bits64(x)                                         \
  (idris2_mkBits64((uint64_t)idris2_vp_to_Bits8(x)))
#define idris2_cast_Bits8_to_Int8(x) (x)
#define idris2_cast_Bits8_to_Int16(x) (x)
#define idris2_cast_Bits8_to_Int32(x) (x)
#define idris2_cast_Bits8_to_Int64(x)                                          \
  (idris2_mkInt64((int64_t)idris2_vp_to_Bits8(x)))
Value *idris2_cast_Bits8_to_Integer(Value *input);
#define idris2_cast_Bits8_to_Double(x)                                         \
  (idris2_mkDouble((double)idris2_vp_to_Bits8(x)))
#define idris2_cast_Bits8_to_Char(x)                                           \
  (idris2_mkChar((uint32_t)idris2_vp_to_Bits8(x)))
Value *idris2_cast_Bits8_to_String(Value *input);

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
Value *idris2_cast_Bits16_to_Integer(Value *input);
#define idris2_cast_Bits16_to_Double(x)                                        \
  (idris2_mkDouble((double)idris2_vp_to_Bits16(x)))
#define idris2_cast_Bits16_to_Char(x)                                          \
  (idris2_mkChar(idris2_validCodePoint((uint32_t)idris2_vp_to_Bits16(x))))
Value *idris2_cast_Bits16_to_String(Value *input);

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
Value *idris2_cast_Bits32_to_Integer(Value *input);
#define idris2_cast_Bits32_to_Double(x)                                        \
  (idris2_mkDouble((double)idris2_vp_to_Bits32(x)))
#define idris2_cast_Bits32_to_Char(x)                                          \
  (idris2_mkChar(idris2_validCodePoint((uint32_t)idris2_vp_to_Bits32(x))))
Value *idris2_cast_Bits32_to_String(Value *input);

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
Value *idris2_cast_Bits64_to_Integer(Value *input);
#define idris2_cast_Bits64_to_Double(x)                                        \
  (idris2_mkDouble((double)idris2_vp_to_Bits64(x)))
#define idris2_cast_Bits64_to_Char(x)                                          \
  (idris2_mkChar(idris2_validCodePoint((uint32_t)idris2_vp_to_Bits64(x))))
Value *idris2_cast_Bits64_to_String(Value *input);

Value *idris2_cast_Integer_to_Bits8(Value *input);
Value *idris2_cast_Integer_to_Bits16(Value *input);
Value *idris2_cast_Integer_to_Bits32(Value *input);
Value *idris2_cast_Integer_to_Bits64(Value *input);
Value *idris2_cast_Integer_to_Int8(Value *input);
Value *idris2_cast_Integer_to_Int16(Value *input);
Value *idris2_cast_Integer_to_Int32(Value *input);
Value *idris2_cast_Integer_to_Int64(Value *input);
Value *idris2_cast_Integer_to_Double(Value *input);
Value *idris2_cast_Integer_to_Char(Value *input);
Value *idris2_cast_Integer_to_String(Value *input);
