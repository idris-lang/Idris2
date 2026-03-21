#pragma once

#include <stddef.h>
#include <stdint.h>

/*
 * Minimal UTF-8 encode/decode helpers for the RefC string primitives.
 *
 * All functions operate on NUL-terminated UTF-8 byte strings and treat
 * Idris Char as a Unicode code point (uint32_t, range 0..0x10FFFF).
 *
 * None of these functions allocate heap memory.
 */

/*
 * utf8_encode — encode a Unicode code point to UTF-8.
 *
 * Writes at most 4 bytes to buf (no NUL terminator).
 * Returns the number of bytes written (1..4).
 * Invalid code points (> 0x10FFFF) are encoded as U+FFFD (3 bytes).
 */
static inline int utf8_encode(uint32_t cp, char *buf) {
  if (cp <= 0x7F) {
    buf[0] = (char)cp;
    return 1;
  } else if (cp <= 0x7FF) {
    buf[0] = (char)(0xC0 | (cp >> 6));
    buf[1] = (char)(0x80 | (cp & 0x3F));
    return 2;
  } else if (cp <= 0xFFFF) {
    buf[0] = (char)(0xE0 | (cp >> 12));
    buf[1] = (char)(0x80 | ((cp >> 6) & 0x3F));
    buf[2] = (char)(0x80 | (cp & 0x3F));
    return 3;
  } else if (cp <= 0x10FFFF) {
    buf[0] = (char)(0xF0 | (cp >> 18));
    buf[1] = (char)(0x80 | ((cp >> 12) & 0x3F));
    buf[2] = (char)(0x80 | ((cp >> 6) & 0x3F));
    buf[3] = (char)(0x80 | (cp & 0x3F));
    return 4;
  } else {
    /* U+FFFD replacement character */
    buf[0] = (char)0xEF;
    buf[1] = (char)0xBF;
    buf[2] = (char)0xBD;
    return 3;
  }
}

/*
 * utf8_decode — decode the first UTF-8 code point from s.
 *
 * Stores the code point in *out_cp.
 * Returns the number of bytes consumed (1..4).
 * On invalid input the offending byte is returned as-is (1 byte consumed).
 */
static inline int utf8_decode(const char *s, uint32_t *out_cp) {
  unsigned char b0 = (unsigned char)s[0];
  if (b0 < 0x80) {
    *out_cp = b0;
    return 1;
  } else if ((b0 & 0xE0) == 0xC0) {
    unsigned char b1 = (unsigned char)s[1];
    if ((b1 & 0xC0) == 0x80) {
      *out_cp = ((uint32_t)(b0 & 0x1F) << 6) | (b1 & 0x3F);
      return 2;
    }
  } else if ((b0 & 0xF0) == 0xE0) {
    unsigned char b1 = (unsigned char)s[1];
    unsigned char b2 = (unsigned char)s[2];
    if ((b1 & 0xC0) == 0x80 && (b2 & 0xC0) == 0x80) {
      *out_cp = ((uint32_t)(b0 & 0x0F) << 12) | ((uint32_t)(b1 & 0x3F) << 6) |
                (uint32_t)(b2 & 0x3F);
      return 3;
    }
  } else if ((b0 & 0xF8) == 0xF0) {
    unsigned char b1 = (unsigned char)s[1];
    unsigned char b2 = (unsigned char)s[2];
    unsigned char b3 = (unsigned char)s[3];
    if ((b1 & 0xC0) == 0x80 && (b2 & 0xC0) == 0x80 && (b3 & 0xC0) == 0x80) {
      *out_cp = ((uint32_t)(b0 & 0x07) << 18) | ((uint32_t)(b1 & 0x3F) << 12) |
                ((uint32_t)(b2 & 0x3F) << 6) | (uint32_t)(b3 & 0x3F);
      return 4;
    }
  }
  /* Invalid byte — consume one byte, emit it as-is */
  *out_cp = b0;
  return 1;
}

/*
 * utf8_seq_len — return the byte length of the UTF-8 sequence starting at s[0].
 * Does not validate continuation bytes.  Returns 1 for invalid lead bytes.
 */
static inline int utf8_seq_len(const char *s) {
  unsigned char b = (unsigned char)s[0];
  if (b < 0x80)
    return 1;
  if ((b & 0xE0) == 0xC0)
    return 2;
  if ((b & 0xF0) == 0xE0)
    return 3;
  if ((b & 0xF8) == 0xF0)
    return 4;
  return 1;
}

/*
 * utf8_cp_count — number of Unicode code points in a NUL-terminated string.
 */
static inline size_t utf8_cp_count(const char *s) {
  size_t n = 0;
  while (*s) {
    s += utf8_seq_len(s);
    n++;
  }
  return n;
}

/*
 * utf8_cp_to_byte_offset — byte offset of the n-th code point (0-based).
 *
 * If n >= number of code points, returns the byte offset of the NUL terminator
 * (i.e. strlen(s)).
 */
static inline size_t utf8_cp_to_byte_offset(const char *s, size_t n) {
  size_t offset = 0;
  while (s[offset] && n > 0) {
    offset += utf8_seq_len(s + offset);
    n--;
  }
  return offset;
}
