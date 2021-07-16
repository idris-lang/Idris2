#include "idris_util.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

void idris2_verify_failed(const char* file, int line, const char* cond, const char* fmt, ...) {
    va_list ap;
    va_start(ap, fmt);

    char message[1000];
    snprintf(message, sizeof(message), fmt, ap);

    fprintf(stderr, "assertion failed in %s:%d: %s: %s\n", file, line, cond, message);
    abort();
}
