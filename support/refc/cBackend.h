#pragma once

#include "idris2_config.h"

#ifndef IDRIS2_NO_THREADS
#include <pthread.h>
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "_datatypes.h"
#include "buffer.h"
#include "casts.h"
#include "clock.h"
#include "concurrency.h"
#include "mathFunctions.h"
#include "memoryManagement.h"
#include "prim.h"
#include "runtime.h"
#include "stringOps.h"
#include "struct_support.h"
#include "threads.h"
