#include "clock.h"

#define NSEC_PER_SEC 1000000000
#define CLOCKS_PER_NSEC ((float)CLOCKS_PER_SEC / NSEC_PER_SEC)

Value *clockTimeMonotonic(void) { return clockTimeUtc(); }

Value *clockTimeUtc(void) {
  return (Value *)idris2_mkBits64(time(NULL) * NSEC_PER_SEC);
}

Value *clockTimeProcess(void) {
  uint64_t time_ns = clock() / CLOCKS_PER_NSEC;
  return (Value *)idris2_mkBits64(time_ns);
}

Value *clockTimeThread(void) { return clockTimeProcess(); }

Value *clockTimeGcCpu(void) { return NULL; }

Value *clockTimeGcReal(void) { return NULL; }

int clockValid(Value *clock) { return clock != NULL; }

uint64_t clockSecond(Value *clock) {
  return idris2_vp_to_Bits64(clock) / NSEC_PER_SEC;
}

uint64_t clockNanosecond(Value *clock) {
  return idris2_vp_to_Bits64(clock) % NSEC_PER_SEC;
}
