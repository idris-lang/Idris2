#include "threads.h"
#include "refc_util.h"

#include <string.h>

#ifndef IDRIS2_NO_THREADS

/*
 * Thread entry point.
 *
 * The closure passed to refc_fork is a PrimIO () — a closure that expects one
 * argument (the RealWorld token, always NULL in RefC) and returns unit.
 * We apply it, run the trampoline to force any thunks, then drop the result
 * and clean up.
 */
static void *refc_thread_entry(void *arg) {
  Value_Closure *fct = (Value_Closure *)arg;

  /* Apply the closure to the world token (NULL).
   * idris2_apply_closure already trampolines the result, and
   * idris2_tailcall_apply_closure consumes fct's reference (via
   * idris2_isUnique / free or --refCounter), so we must NOT call
   * idris2_removeReference(fct) here — that would double-free. */
  Value *result = idris2_apply_closure((Value *)fct, NULL);
  idris2_removeReference(result);

  return NULL;
}

/*
 * refc_fork — spawn a new OS thread running `fct`.
 *
 * Corresponds to:
 *   %foreign "C:refc_fork"
 *   prim__fork : (1 prog : PrimIO ()) -> PrimIO ThreadID
 *
 * Returns a Value_Thread* boxed as a Value*, which the caller can pass to
 * refc_threadWait.
 */
Value *refc_fork(Value_Closure *fct) {
  /* Keep the closure alive for the duration of the thread. */
  idris2_newReference((Value *)fct);

  Value_Thread *t = IDRIS2_NEW_VALUE(Value_Thread);
  t->header.tag = THREAD_TAG;

  int r = pthread_create(&t->thread, NULL, refc_thread_entry, (void *)fct);
  IDRIS2_REFC_VERIFY(!r, "pthread_create failed: %s", strerror(r));

  return (Value *)t;
}

/*
 * refc_threadWait — wait for a thread spawned by refc_fork to finish.
 *
 * Corresponds to:
 *   %foreign "C:refc_threadWait"
 *   prim__threadWait : (1 threadID : ThreadID) -> PrimIO ()
 */
Value *refc_threadWait(Value *threadID) {
  Value_Thread *t = (Value_Thread *)threadID;
  int r = pthread_join(t->thread, NULL);
  IDRIS2_REFC_VERIFY(!r, "pthread_join failed: %s", strerror(r));
  return NULL;
}

#else /* IDRIS2_NO_THREADS */

Value *refc_fork(Value_Closure *fct) {
  (void)fct;
  IDRIS2_REFC_VERIFY(0, "refc_fork: threads not available "
                        "(compiled with IDRIS2_NO_THREADS)");
  return NULL;
}

Value *refc_threadWait(Value *threadID) {
  (void)threadID;
  IDRIS2_REFC_VERIFY(0, "refc_threadWait: threads not available "
                        "(compiled with IDRIS2_NO_THREADS)");
  return NULL;
}

#endif /* IDRIS2_NO_THREADS */
