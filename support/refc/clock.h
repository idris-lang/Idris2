#pragma once

#ifndef IDRIS2_NO_CLOCK
#  include <time.h>
#endif

#include "cBackend.h"

Value *clockTimeMonotonic(void);
Value *clockTimeUtc(void);
Value *clockTimeProcess(void);
Value *clockTimeThread(void);
Value *clockTimeGcCpu(void);
Value *clockTimeGcReal(void);

int clockValid(Value *clock);
uint64_t clockSecond(Value *clock);
uint64_t clockNanosecond(Value *clock);
