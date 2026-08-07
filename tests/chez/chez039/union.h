#include <stdint.h>

#pragma once

typedef union {
  int x;
  double y;
} intOrDouble;

intOrDouble *mkInt(int x);
intOrDouble *mkDouble(double x);
void freeIntOrDouble(intOrDouble *pt);

typedef union {
  struct {
    uint8_t tag0;
    int x;
  };
  struct {
    uint8_t tag1;
    double y;
    int z;
  };
} taggedUnion;

taggedUnion *mkTaggedUnion0(int x);
taggedUnion *mkTaggedUnion1(double y, int z);
void freeTaggedUnion(taggedUnion *pt);
