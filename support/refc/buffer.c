#include "buffer.h"
#include "refc_util.h"
#include <string.h>
#include <sys/stat.h>

void *newBuffer(int bytes) {
  size_t size = sizeof(Buffer) + bytes * sizeof(uint8_t);

  Buffer *buf = malloc(size);
  if (buf == NULL) {
    return NULL;
  }

  buf->size = bytes;
  memset(buf->data, 0, bytes);

  return (void *)buf;
}

static void assert_valid_range(Buffer *buf, int64_t offset, int64_t len) {
  IDRIS2_REFC_VERIFY(offset >= 0, "offset (%lld) < 0", (long long)offset);
  IDRIS2_REFC_VERIFY(len >= 0, "len (%lld) < 0", (long long)len);
  IDRIS2_REFC_VERIFY(offset + len <= buf->size,
                     "offset (%lld) + len (%lld) > buf.size (%lld)",
                     (long long)offset, (long long)len, (long long)buf->size);
}

void copyBuffer(void *from, int from_offset, int len, void *to, int to_offset) {
  Buffer *bfrom = from;
  Buffer *bto = to;

  assert_valid_range(bfrom, from_offset, len);
  assert_valid_range(bto, to_offset, len);

  memcpy(bto->data + to_offset, bfrom->data + from_offset, len);
}

int getBufferSize(void *buffer) { return ((Buffer *)buffer)->size; }

void setBufferByte(void *buffer, int loc, int byte) {
  Buffer *b = buffer;

  assert_valid_range(buffer, loc, 1);

  b->data[loc] = byte;
}

void setBufferInt(void *buffer, int loc, int64_t val) {
  Buffer *b = buffer;
  assert_valid_range(b, loc, 8);
  b->data[loc] = val & 0xff;
  b->data[loc + 1] = (val >> 8) & 0xff;
  b->data[loc + 2] = (val >> 16) & 0xff;
  b->data[loc + 3] = (val >> 24) & 0xff;
  b->data[loc + 4] = (val >> 32) & 0xff;
  b->data[loc + 5] = (val >> 40) & 0xff;
  b->data[loc + 6] = (val >> 48) & 0xff;
  b->data[loc + 7] = (val >> 56) & 0xff;
}

void setBufferDouble(void *buffer, int loc, double val) {
  Buffer *b = buffer;
  assert_valid_range(b, loc, sizeof(double));
  unsigned char *c = (unsigned char *)(&val);
  int i;
  for (i = 0; i < sizeof(double); ++i) {
    b->data[loc + i] = c[i];
  }
}

void setBufferString(void *buffer, int loc, char *str) {
  Buffer *b = buffer;
  size_t len = strlen(str);
  assert_valid_range(b, loc, len);
  memcpy((b->data) + loc, str, len);
}

uint8_t getBufferByte(void *buffer, int loc) {
  Buffer *b = buffer;
  assert_valid_range(b, loc, 1);
  return b->data[loc];
}

int64_t getBufferInt(void *buffer, int loc) {
  Buffer *b = buffer;
  assert_valid_range(b, loc, 8);
  int64_t result = 0;
  for (size_t i = 0; i < 8; i++) {
    result |= (uint64_t)(uint8_t)b->data[loc + i] << (8 * i);
  }
  return result;
}

double getBufferDouble(void *buffer, int loc) {
  Buffer *b = buffer;
  assert_valid_range(b, loc, sizeof(double));
  double d;
  // I am even less proud of this
  unsigned char *c = (unsigned char *)(&d);
  int i;
  for (i = 0; i < sizeof(double); ++i) {
    c[i] = b->data[loc + i];
  }
  return d;
}

char *getBufferString(void *buffer, int loc, int len) {
  Buffer *b = buffer;
  assert_valid_range(b, loc, len);
  char *s = (char *)(b->data + loc);
  char *rs = malloc(len + 1);
  strncpy(rs, s, len);
  rs[len] = '\0';
  return rs;
}
