#include "struct.h"
#include <stdio.h>
#include <stdlib.h>

char *getString(void *p) { return (char *)p; }

point *mkPoint(int x, int y) {
  point *pt = malloc(sizeof(point));
  pt->x = x;
  pt->y = y;
  return pt;
}

void freePoint(point *pt) { free(pt); }

namedpoint *mkNamedPoint(char *str, point *p) {
  namedpoint *np = malloc(sizeof(namedpoint));
  np->name = str;
  np->pt = p;
  printf("Made it!\n");

  return np;
}

void freeNamedPoint(namedpoint *np) { free(np); }

inlinedpoint *mkInlinedPoint(char *str, int x, int y) {
  inlinedpoint *ip = malloc(sizeof(inlinedpoint));
  point pt;
  pt.x = x;
  pt.y = y;
  ip->name = str;
  ip->pt = pt;
  printf("Made it inlined!\n");

  return ip;
}

void freeInlinedPoint(inlinedpoint *ip) { free(ip); }
