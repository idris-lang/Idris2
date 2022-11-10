#pragma once

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct {
  int size;
  char data[];
} Buffer;

void *newBuffer(int bytes);

int getBufferSize(void *buffer);

void setBufferUIntLE(void *buffer, int loc, uint64_t val, size_t len);
#define setBufferUInt8(b, l, v)                                                \
  do {                                                                         \
    setBufferUIntLE(b, l, (uint64_t)v, 1);                                     \
  } while (0)
#define setBufferUInt16LE(b, l, v)                                             \
  do {                                                                         \
    setBufferUIntLE(b, l, (uint64_t)v, 2);                                     \
  } while (0)
#define setBufferUInt32LE(b, l, v)                                             \
  do {                                                                         \
    setBufferUIntLE(b, l, (uint64_t)v, 4);                                     \
  } while (0)
#define setBufferUInt64LE(b, l, v)                                             \
  do {                                                                         \
    setBufferUIntLE(b, l, (uint64_t)v, 8);                                     \
  } while (0)

#define setBufferByte(b, l, v)                                                 \
  do {                                                                         \
    setBufferUIntLE(b, l, (uint64_t)v, 1);                                     \
  } while (0)
#define setBufferInt16LE(b, l, v)                                              \
  do {                                                                         \
    setBufferUIntLE(b, l, (uint64_t)v, 2);                                     \
  } while (0)
#define setBufferInt32LE(b, l, v)                                              \
  do {                                                                         \
    setBufferUIntLE(b, l, (uint64_t)v, 4);                                     \
  } while (0)
#define setBufferInt64LE(b, l, v)                                              \
  do {                                                                         \
    setBufferUIntLE(b, l, (uint64_t)v, 8);                                     \
  } while (0)

void setBufferDouble(void *buffer, int loc, double val);
void setBufferString(void *buffer, int loc, char *str);

void copyBuffer(void *from, int start, int len, void *to, int loc);

uint64_t getBufferUIntLE(void *buffer, int loc, size_t len);
#define getBufferUInt8(b, l) ((uint8_t)getBufferUIntLE(b, l, 1))
#define getBufferUInt16LE(b, l) ((uint16_t)getBufferUIntLE(b, l, 2))
#define getBufferUInt32LE(b, l) ((uint32_t)getBufferUIntLE(b, l, 4))
#define getBufferUInt64LE(b, l) ((uint64_t)getBufferUIntLE(b, l, 8))

#define getBufferByte(b, l) ((int64_t)getBufferUIntLE(b, l, 1))
#define getBufferInt16LE(b, l) ((int64_t)getBufferUIntLE(b, l, 2))
#define getBufferInt32LE(b, l) ((int64_t)getBufferUIntLE(b, l, 4))
#define getBufferInt64LE(b, l) ((int64_t)getBufferUIntLE(b, l, 8))
double getBufferDouble(void *buffer, int loc);
char *getBufferString(void *buffer, int loc, int len);
