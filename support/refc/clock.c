#include "clock.h"

#define NSEC_PER_SEC 1000000000

#ifdef IDRIS2_NO_CLOCK

/* Bare-metal stub: no POSIX time source available.
 * All clock functions return 0.  Override these symbols in your
 * application if the target has an RTC or cycle counter. */

Value *clockTimeMonotonic(void) { return (Value *)idris2_mkBits64(0); }
Value *clockTimeUtc(void)       { return (Value *)idris2_mkBits64(0); }
Value *clockTimeProcess(void)   { return (Value *)idris2_mkBits64(0); }
Value *clockTimeThread(void)    { return (Value *)idris2_mkBits64(0); }

#else /* !IDRIS2_NO_CLOCK */

#include <time.h>
#define CLOCKS_PER_NSEC ((float)CLOCKS_PER_SEC / NSEC_PER_SEC)

Value *clockTimeMonotonic(void) { return clockTimeUtc(); }

Value *clockTimeUtc(void) {
  return (Value *)idris2_mkBits64((uint64_t)time(NULL) * NSEC_PER_SEC);
}

Value *clockTimeProcess(void) {
  uint64_t time_ns = (uint64_t)((float)clock() / CLOCKS_PER_NSEC);
  return (Value *)idris2_mkBits64(time_ns);
}

Value *clockTimeThread(void) { return clockTimeProcess(); }

#endif /* IDRIS2_NO_CLOCK */

Value *clockTimeGcCpu(void)  { return NULL; }
Value *clockTimeGcReal(void) { return NULL; }

int clockValid(Value *clock) { return clock != NULL; }

uint64_t clockSecond(Value *clock) {
  return idris2_vp_to_Bits64(clock) / NSEC_PER_SEC;
}

uint64_t clockNanosecond(Value *clock) {
  return idris2_vp_to_Bits64(clock) % NSEC_PER_SEC;
}
