#pragma once

typedef struct {
  int x;
  int y;
} point;

typedef struct {
  char *name;
  point *pt;
} namedpoint;

typedef struct {
  char *name;
  point pt;
} inlinedpoint;

point *mkPoint(int x, int y);
void freePoint(point *pt);

namedpoint *mkNamedPoint(char *str, point *p);
void freeNamedPoint(namedpoint *np);

inlinedpoint *mkInlinedPoint(char *str, int x, int y);
void freeInlinedPoint(inlinedpoint *it);

char *getString(void *p);
