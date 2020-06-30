#include <stdlib.h>
#include <stdio.h>

int add(int x, int y) {
    return x+y;
}

int addWithMessage(char* msg, int x, int y) {
    printf("%s: %d + %d = %d\n", msg, x, y, x+y);
    return x+y;
}

typedef char*(*StringFn)(char*, int);

char* applyFn(char* x, int y, StringFn f) {
    printf("Applying callback to %s %d\n", x, y);
    return f(x, y);
}

char* applyFnPure(char* x, int y, StringFn f) {
    return f(x, y);
}

typedef struct {
    int x;
    int y;
} point;

point* mkPoint(int x, int y) {
    point* pt = malloc(sizeof(point));
    pt->x = x;
    pt->y = y;
    return pt;
}

void freePoint(point* pt) {
    free(pt);
}

