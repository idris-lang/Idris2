#include "union.h"
#include <stdio.h>
#include <stdlib.h>

intOrDouble *mkInt(int x) {
  intOrDouble *pt = malloc(sizeof(intOrDouble));
  pt->x = x;
  return pt;
}

intOrDouble *mkDouble(double y) {
  intOrDouble *pt = malloc(sizeof(intOrDouble));
  pt->y = y;
  return pt;
}

void freeIntOrDouble(intOrDouble *pt) { free(pt); }

taggedUnion *mkTaggedUnion0(int x) {
  taggedUnion *un = malloc(sizeof(taggedUnion));
  un->tag0 = 0;
  un->x = x;
  return un;
}

taggedUnion *mkTaggedUnion1(double y, int z) {
  taggedUnion *un = malloc(sizeof(taggedUnion));
  un->tag1 = 1;
  un->y = y;
  un->z = z;
  return un;
}

void freeTaggedUnion(taggedUnion *un) { free(un); }
