#include "refc_util.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>

void idris2_refc_verify_failed(const char *file, int line, const char *cond,
                               const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);

  char message[1024];
  vsnprintf(message, sizeof(message), fmt, ap);

  fprintf(stderr, "\nIdris2 runtime assertion failed\n"
                  "  location : %s:%d\n"
                  "  condition: %s\n"
                  "  detail   : %s\n",
          file, line, cond, message);
  fflush(stderr);
  abort();
}
