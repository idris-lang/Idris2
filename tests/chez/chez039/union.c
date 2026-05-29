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
