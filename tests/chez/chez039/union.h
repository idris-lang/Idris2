#pragma once

typedef union {
  int x;
  double y;
} intOrDouble;

intOrDouble *mkInt(int x);
intOrDouble *mkDouble(double x);
void freeIntOrDouble(intOrDouble *pt);
