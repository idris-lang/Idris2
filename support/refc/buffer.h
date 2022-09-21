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

void setBufferWordLE(void *buffer, int loc, uint64_t val, size_t len);
#define setBufferWord8(b, l, v)                                                \
  do {                                                                         \
    setBufferWordLE(b, l, (uint64_t)v, 1);                                     \
  } while (0)
#define setBufferWord16LE(b, l, v)                                             \
  do {                                                                         \
    setBufferWordLE(b, l, (uint64_t)v, 2);                                     \
  } while (0)
#define setBufferWord32LE(b, l, v)                                             \
  do {                                                                         \
    setBufferWordLE(b, l, (uint64_t)v, 4);                                     \
  } while (0)
#define setBufferWord64LE(b, l, v)                                             \
  do {                                                                         \
    setBufferWordLE(b, l, (uint64_t)v, 8);                                     \
  } while (0)

#define setBufferByte(b, l, v)                                                 \
  do {                                                                         \
    setBufferWordLE(b, l, (uint64_t)v, 1);                                     \
  } while (0)
#define setBufferInt16LE(b, l, v)                                              \
  do {                                                                         \
    setBufferWordLE(b, l, (uint64_t)v, 2);                                     \
  } while (0)
#define setBufferInt32LE(b, l, v)                                              \
  do {                                                                         \
    setBufferWordLE(b, l, (uint64_t)v, 4);                                     \
  } while (0)
#define setBufferInt64LE(b, l, v)                                              \
  do {                                                                         \
    setBufferWordLE(b, l, (uint64_t)v, 8);                                     \
  } while (0)

void setBufferDouble(void *buffer, int loc, double val);
void setBufferString(void *buffer, int loc, char *str);

void copyBuffer(void *from, int start, int len, void *to, int loc);

uint64_t getBufferWordLE(void *buffer, int loc, size_t len);
#define getBufferWord8(b, l) ((uint8_t)getBufferWordLE(b, l, 1))
#define getBufferWord16LE(b, l) ((uint16_t)getBufferWordLE(b, l, 2))
#define getBufferWord32LE(b, l) ((uint32_t)getBufferWordLE(b, l, 4))
#define getBufferWord64LE(b, l) ((uint64_t)getBufferWordLE(b, l, 8))

#define getBufferByte(b, l) ((int64_t)getBufferWordLE(b, l, 1))
#define getBufferInt16LE(b, l) ((int64_t)getBufferWordLE(b, l, 2))
#define getBufferInt32LE(b, l) ((int64_t)getBufferWordLE(b, l, 4))
#define getBufferInt64LE(b, l) ((int64_t)getBufferWordLE(b, l, 8))
double getBufferDouble(void *buffer, int loc);
char *getBufferString(void *buffer, int loc, int len);
