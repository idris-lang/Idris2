#pragma once
#include <stdint.h>

typedef struct {
    int32_t x;
    int32_t y;
} point;

typedef struct {
    char   *name;
    point  *pt;
} namedpoint;

point      *mkPoint(int32_t x, int32_t y);
void        freePoint(point *pt);
namedpoint *mkNamedPoint(char *str, point *p);
void        freeNamedPoint(namedpoint *np);
