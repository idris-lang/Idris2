#include "concurrency.h"
#include "refc_util.h"

#include <string.h>
#include <time.h>

#ifndef IDRIS2_NO_THREADS

/*
 * NOTE: These C functions must NOT call idris2_removeReference on their
 * arguments.  The RefC codegen emits removeReference calls for every
 * argument in the generated wrapper — adding another release here would
 * double-free.  See the analogous pattern in threads.c / refc_threadWait.
 */

/* -------------------------------------------------------------------------
 * Mutex
 * ---------------------------------------------------------------------- */

Value *refc_makeMutex(void) {
  Value_Mutex *m = IDRIS2_NEW_VALUE(Value_Mutex);
  m->header.tag = MUTEX_TAG;
  m->mutex = (pthread_mutex_t *)malloc(sizeof(pthread_mutex_t));
  IDRIS2_REFC_VERIFY(m->mutex, "malloc failed");
  int r = pthread_mutex_init(m->mutex, NULL);
  IDRIS2_REFC_VERIFY(!r, "pthread_mutex_init failed: %s", strerror(r));
  return (Value *)m;
}

Value *refc_mutexAcquire(Value *mutex) {
  int r = pthread_mutex_lock(((Value_Mutex *)mutex)->mutex);
  IDRIS2_REFC_VERIFY(!r, "pthread_mutex_lock failed: %s", strerror(r));
  return NULL;
}

Value *refc_mutexRelease(Value *mutex) {
  int r = pthread_mutex_unlock(((Value_Mutex *)mutex)->mutex);
  IDRIS2_REFC_VERIFY(!r, "pthread_mutex_unlock failed: %s", strerror(r));
  return NULL;
}

/* -------------------------------------------------------------------------
 * Condition variable
 * ---------------------------------------------------------------------- */

Value *refc_makeCondition(void) {
  Value_Condition *c = IDRIS2_NEW_VALUE(Value_Condition);
  c->header.tag = CONDITION_TAG;
  c->cond = (pthread_cond_t *)malloc(sizeof(pthread_cond_t));
  IDRIS2_REFC_VERIFY(c->cond, "malloc failed");
  int r = pthread_cond_init(c->cond, NULL);
  IDRIS2_REFC_VERIFY(!r, "pthread_cond_init failed: %s", strerror(r));
  return (Value *)c;
}

Value *refc_conditionWait(Value *cond, Value *mutex) {
  int r = pthread_cond_wait(((Value_Condition *)cond)->cond,
                            ((Value_Mutex *)mutex)->mutex);
  IDRIS2_REFC_VERIFY(!r, "pthread_cond_wait failed: %s", strerror(r));
  return NULL;
}

Value *refc_conditionWaitTimeout(Value *cond, Value *mutex, int64_t timeout_us) {
  struct timespec t;
  clock_gettime(CLOCK_REALTIME, &t);
  t.tv_sec  += timeout_us / 1000000;
  t.tv_nsec += (timeout_us % 1000000) * 1000;
  if (t.tv_nsec >= 1000000000L) {
    t.tv_sec++;
    t.tv_nsec -= 1000000000L;
  }
  /* timedwait returns ETIMEDOUT on timeout — that is normal, not an error. */
  pthread_cond_timedwait(((Value_Condition *)cond)->cond,
                         ((Value_Mutex *)mutex)->mutex, &t);
  return NULL;
}

Value *refc_conditionSignal(Value *cond) {
  int r = pthread_cond_signal(((Value_Condition *)cond)->cond);
  IDRIS2_REFC_VERIFY(!r, "pthread_cond_signal failed: %s", strerror(r));
  return NULL;
}

Value *refc_conditionBroadcast(Value *cond) {
  int r = pthread_cond_broadcast(((Value_Condition *)cond)->cond);
  IDRIS2_REFC_VERIFY(!r, "pthread_cond_broadcast failed: %s", strerror(r));
  return NULL;
}

/* -------------------------------------------------------------------------
 * Semaphore  (mutex + condvar + counter, portable across macOS and Linux)
 * ---------------------------------------------------------------------- */

Value *refc_makeSemaphore(int64_t init) {
  Value_Semaphore *s = IDRIS2_NEW_VALUE(Value_Semaphore);
  s->header.tag = SEMAPHORE_TAG;
  s->count = (int)init;
  int r = pthread_mutex_init(&s->mutex, NULL);
  IDRIS2_REFC_VERIFY(!r, "pthread_mutex_init failed: %s", strerror(r));
  r = pthread_cond_init(&s->cond, NULL);
  IDRIS2_REFC_VERIFY(!r, "pthread_cond_init failed: %s", strerror(r));
  return (Value *)s;
}

Value *refc_semaphorePost(Value *sema) {
  Value_Semaphore *s = (Value_Semaphore *)sema;
  pthread_mutex_lock(&s->mutex);
  s->count++;
  pthread_cond_signal(&s->cond);
  pthread_mutex_unlock(&s->mutex);
  return NULL;
}

Value *refc_semaphoreWait(Value *sema) {
  Value_Semaphore *s = (Value_Semaphore *)sema;
  pthread_mutex_lock(&s->mutex);
  while (s->count == 0)
    pthread_cond_wait(&s->cond, &s->mutex);
  s->count--;
  pthread_mutex_unlock(&s->mutex);
  return NULL;
}

/* -------------------------------------------------------------------------
 * Barrier  (mutex + condvar + counters, portable)
 * ---------------------------------------------------------------------- */

Value *refc_makeBarrier(int64_t numThreads) {
  Value_Barrier *b = IDRIS2_NEW_VALUE(Value_Barrier);
  b->header.tag = BARRIER_TAG;
  b->total   = (int)numThreads;
  b->arrived = 0;
  int r = pthread_mutex_init(&b->mutex, NULL);
  IDRIS2_REFC_VERIFY(!r, "pthread_mutex_init failed: %s", strerror(r));
  r = pthread_cond_init(&b->cond, NULL);
  IDRIS2_REFC_VERIFY(!r, "pthread_cond_init failed: %s", strerror(r));
  return (Value *)b;
}

Value *refc_barrierWait(Value *barrier) {
  Value_Barrier *b = (Value_Barrier *)barrier;
  pthread_mutex_lock(&b->mutex);
  b->arrived++;
  if (b->arrived == b->total) {
    b->arrived = 0;
    pthread_cond_broadcast(&b->cond);
  } else {
    while (b->arrived != 0)
      pthread_cond_wait(&b->cond, &b->mutex);
  }
  pthread_mutex_unlock(&b->mutex);
  return NULL;
}

#endif /* IDRIS2_NO_THREADS */
