#include "clock.h"

#define NSEC_PER_SEC 1000000000
#define CLOCKS_PER_NSEC ((float)CLOCKS_PER_SEC / NSEC_PER_SEC)

Idris2_Value *clockTimeMonotonic() { return clockTimeUtc(); }

Idris2_Value *clockTimeUtc() {
  return (Idris2_Value *)idris2_mkBits64(time(NULL) * NSEC_PER_SEC);
}

Idris2_Value *clockTimeProcess() {
  uint64_t time_ns = clock() / CLOCKS_PER_NSEC;
  return (Idris2_Value *)idris2_mkBits64(time_ns);
}

Idris2_Value *clockTimeThread() { return clockTimeProcess(); }

Idris2_Value *clockTimeGcCpu() { return NULL; }

Idris2_Value *clockTimeGcReal() { return NULL; }

int clockValid(Idris2_Value *clock) { return clock != NULL; }

uint64_t clockSecond(Idris2_Value *clock) {
  return idris2_vp_to_Bits64(clock) / NSEC_PER_SEC;
}

uint64_t clockNanosecond(Idris2_Value *clock) {
  return idris2_vp_to_Bits64(clock) % NSEC_PER_SEC;
}
