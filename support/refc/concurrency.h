#pragma once
#include "cBackend.h"

/* Mutex */
Value *refc_makeMutex(void);
Value *refc_mutexAcquire(Value *mutex);
Value *refc_mutexRelease(Value *mutex);

/* Condition variable */
Value *refc_makeCondition(void);
Value *refc_conditionWait(Value *cond, Value *mutex);
Value *refc_conditionWaitTimeout(Value *cond, Value *mutex, int64_t timeout_us);
Value *refc_conditionSignal(Value *cond);
Value *refc_conditionBroadcast(Value *cond);

/* Semaphore  (init : Int) */
Value *refc_makeSemaphore(int64_t init);
Value *refc_semaphorePost(Value *sema);
Value *refc_semaphoreWait(Value *sema);

/* Barrier  (numThreads : Int) */
Value *refc_makeBarrier(int64_t numThreads);
Value *refc_barrierWait(Value *barrier);
