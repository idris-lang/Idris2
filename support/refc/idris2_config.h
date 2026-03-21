#pragma once

/*
 * idris2_config.h — compile-time feature flags for the RefC runtime.
 *
 * All flags are OFF by default (full-featured hosted build).
 * Pass -D<FLAG> to the C compiler to enable them, e.g. in CC.idr via
 * the directive mechanism or in the runtime Makefile via CPPFLAGS.
 *
 * IDRIS2_NO_GMP
 *   Replace arbitrary-precision Integer (GMP mpz_t) with a 64-bit
 *   signed integer (int64_t).  Integer literals that overflow 63 bits
 *   will silently wrap.  Removes the -lgmp link dependency.
 *   Use for embedded targets or environments where GMP is unavailable.
 *
 * IDRIS2_NO_THREADS
 *   Disable all pthread usage.  Calling fork/mutex/condvar primitives
 *   will abort at runtime with an explanatory message.  Removes the
 *   -lpthread link dependency and avoids _Atomic / stdatomic costs on
 *   single-threaded platforms.
 *
 * IDRIS2_NO_STDIO
 *   Exclude all <stdio.h> / fprintf / vsnprintf usage from the runtime.
 *   Fatal-error messages are suppressed (only IDRIS2_ABORT fires).
 *   Override IDRIS2_WRITE_STDERR below to route diagnostics to a UART
 *   or other bare-metal output channel.
 *   Implied automatically for bare-metal target triples (arm-none-eabi
 *   etc.) when using --directive "target=<triple>" in CC.idr.
 *
 * IDRIS2_NO_CLOCK
 *   Stub out time() / clock() calls in clock.c.  All clock functions
 *   return 0.  Use on bare-metal targets that have no POSIX time source.
 *   Override the stubs by providing your own implementation of the
 *   clockTime* symbols after linking libidris2_refc.
 *   Implied automatically for bare-metal target triples in CC.idr.
 *
 * IDRIS2_MALLOC / IDRIS2_REALLOC / IDRIS2_FREE
 *   Override the heap allocator.  Define all three before including any
 *   RefC header to redirect every allocation through your own functions,
 *   e.g. a pool allocator or a platform-specific heap on bare metal.
 *   Default: the standard-library malloc / realloc / free.
 *
 * IDRIS2_ABORT
 *   Override the fatal-error handler used by IDRIS2_REFC_VERIFY.
 *   Should not return.  Default: abort() from <stdlib.h>.
 *
 * IDRIS2_WRITE_STDERR(msg)
 *   Override the diagnostic output channel.  msg is a const char *.
 *   Default: fputs(msg, stderr) when IDRIS2_NO_STDIO is not set,
 *   no-op when IDRIS2_NO_STDIO is set.
 *   Example for a UART-based bare-metal target:
 *     #define IDRIS2_WRITE_STDERR(msg) uart_puts(msg)
 */

/* -----------------------------------------------------------------------
 * Memory allocator hooks
 * -------------------------------------------------------------------- */

#ifndef IDRIS2_MALLOC
#include <stdlib.h>
#define IDRIS2_MALLOC(sz) malloc(sz)
#define IDRIS2_REALLOC(p, sz) realloc((p), (sz))
#define IDRIS2_FREE(p) free(p)
#endif

#ifndef IDRIS2_ABORT
#include <stdlib.h>
#define IDRIS2_ABORT() abort()
#endif

/* -----------------------------------------------------------------------
 * Diagnostic output hook
 * -------------------------------------------------------------------- */

#ifndef IDRIS2_WRITE_STDERR
#ifdef IDRIS2_NO_STDIO
#define IDRIS2_WRITE_STDERR(msg) ((void)(msg))
#else
#include <stdio.h>
#define IDRIS2_WRITE_STDERR(msg) fputs((msg), stderr)
#endif
#endif
