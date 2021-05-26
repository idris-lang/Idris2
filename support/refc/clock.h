#ifndef __IDRIS_CLOCK_H__
#define __IDRIS_CLOCK_H__

#include <time.h>

#include "cBackend.h"

Value *clockTimeMonotonic();
Value *clockTimeUtc();
Value *clockTimeProcess();
Value *clockTimeThread();
Value *clockTimeGcCpu();
Value *clockTimeGcReal();

int clockValid(Value *clock);
uint64_t clockSecond(Value *clock);
uint64_t clockNanosecond(Value *clock);

#endif
