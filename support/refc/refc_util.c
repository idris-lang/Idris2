#include "refc_util.h"
#include "idris2_config.h"

#include <stdarg.h>
#ifndef IDRIS2_NO_STDIO
#include <stdio.h>
#endif

void idris2_refc_verify_failed(const char *file, int line, const char *cond,
                               const char *fmt, ...) {
#ifndef IDRIS2_NO_STDIO
  va_list ap;
  va_start(ap, fmt);

  char message[1024];
  vsnprintf(message, sizeof(message), fmt, ap);
  va_end(ap);

  char header[512];
  snprintf(header, sizeof(header),
           "\nIdris2 runtime assertion failed\n"
           "  location : %s:%d\n"
           "  condition: %s\n"
           "  detail   : ",
           file, line, cond);
  IDRIS2_WRITE_STDERR(header);
  IDRIS2_WRITE_STDERR(message);
  IDRIS2_WRITE_STDERR("\n");
#else
  (void)file;
  (void)line;
  (void)cond;
  (void)fmt;
  IDRIS2_WRITE_STDERR("Idris2 runtime assertion failed\n");
#endif
  IDRIS2_ABORT();
}
