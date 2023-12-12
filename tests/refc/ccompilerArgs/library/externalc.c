#include "externalc.h"

int add(int x, int y) { return x + y; }

int fastfibsum(int x) {
  int acc = 0;
  int p = 0;
  int c = 1;
  int tmp;
  for (; 0 <= --x;) {
    acc += c;
    tmp = c;
    c = c + p;
    p = tmp;
  }
  return acc;
}