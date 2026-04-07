#pragma once

#include <time.h>

#include "cBackend.h"

Idris2_Value *clockTimeMonotonic();
Idris2_Value *clockTimeUtc();
Idris2_Value *clockTimeProcess();
Idris2_Value *clockTimeThread();
Idris2_Value *clockTimeGcCpu();
Idris2_Value *clockTimeGcReal();

int clockValid(Idris2_Value *clock);
uint64_t clockSecond(Idris2_Value *clock);
uint64_t clockNanosecond(Idris2_Value *clock);
