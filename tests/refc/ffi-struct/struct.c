#include <stdlib.h>
#include <stdio.h>
#include "struct.h"

point *mkPoint(int32_t x, int32_t y) {
    point *pt = malloc(sizeof(point));
    pt->x = x;
    pt->y = y;
    return pt;
}

void freePoint(point *pt) {
    free(pt);
}

namedpoint *mkNamedPoint(char *str, point *p) {
    namedpoint *np = malloc(sizeof(namedpoint));
    np->name = str;
    np->pt   = p;
    return np;
}

void freeNamedPoint(namedpoint *np) {
    free(np);
}
