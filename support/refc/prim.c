#include "prim.h"
#include "refc_util.h"
#include <string.h>
#include <unistd.h>

Idris2_Value *idris2_Data_IORef_prim__newIORef(Idris2_Value *erased,
                                               Idris2_Value *input_value,
                                               Idris2_Value *_world) {
  Idris2_IORef *ioRef = IDRIS2_NEW_VALUE(Idris2_IORef);
  ioRef->header.tag = IOREF_TAG;
  ioRef->v = idris2_newReference(input_value);
  return (Idris2_Value *)ioRef;
}

Idris2_Value *idris2_Data_IORef_prim__writeIORef(Idris2_Value *erased,
                                                 Idris2_Value *_ioref,
                                                 Idris2_Value *new_value,
                                                 Idris2_Value *_world) {
  Idris2_IORef *ioref = (Idris2_IORef *)_ioref;
  idris2_newReference(new_value);
  Idris2_Value *old = ioref->v;
  ioref->v = new_value;
  idris2_removeReference(old);
  return NULL;
}

// -----------------------------------
//       System operations
// -----------------------------------

Idris2_String const idris2_predefined_osstring = {IDRIS2_STOCKVAL(STRING_TAG),
#ifdef _WIN32
                                                  "windows"
#elif _WIN64
                                                  "windows"
#elif __APPLE__ || __MACH__
                                                  "macOS"
#elif __linux__
                                                  "Linux"
#elif __FreeBSD__
                                                  "FreeBSD"
#elif __OpenBSD__
                                                  "OpenBSD"
#elif __NetBSD__
                                                  "NetBSD"
#elif __DragonFly__
                                                  "DragonFly"
#elif __unix || __unix__
                                                  "Unix"
#else
                                                  "Other"
#endif
};

// NOTE: The codegen is obviously determined at compile time,
//       so the backend should optimize it by replacing it with a constant.
//       It would probably also be useful for conditional compilation.
Idris2_String const idris2_predefined_codegenstring = {
    IDRIS2_STOCKVAL(STRING_TAG), "refc"};

Idris2_Value *idris2_crash(Idris2_Value *msg) {
  Idris2_String *str = (Idris2_String *)msg;
  printf("ERROR: %s\n", str->str);
  exit(-1);
}

//
//
//
// // -----------------------------------
// //         Array operations
// // -----------------------------------

Idris2_Value *idris2_Data_IOArray_Prims_prim__newArray(Idris2_Value *erased,
                                                       Idris2_Value *_length,
                                                       Idris2_Value *v,
                                                       Idris2_Value *_word) {
  int length = idris2_vp_to_Int64(_length);
  Idris2_Array *a = idris2_makeArray(length);

  for (int i = 0; i < length; i++) {
    a->arr[i] = idris2_newReference(v);
  }

  return (Idris2_Value *)a;
}

Idris2_Value *idris2_Data_IOArray_Prims_prim__arraySet(Idris2_Value *erased,
                                                       Idris2_Value *_array,
                                                       Idris2_Value *index,
                                                       Idris2_Value *v,
                                                       Idris2_Value *_word) {
  Idris2_Array *a = (Idris2_Array *)_array;
  idris2_removeReference(a->arr[idris2_vp_to_Int64(index)]);
  a->arr[idris2_vp_to_Int64(index)] = idris2_newReference(v);
  return NULL;
}

//
// -----------------------------------
//      Pointer operations
// -----------------------------------

Idris2_Value *idris2_Prelude_IO_prim__onCollect(Idris2_Value *_erased,
                                                Idris2_Value *_anyPtr,
                                                Idris2_Value *_freeingFunction,
                                                Idris2_Value *_world) {
  Idris2_GCPointer *retVal = IDRIS2_NEW_VALUE(Idris2_GCPointer);
  retVal->header.tag = GC_POINTER_TAG;
  retVal->p = (Idris2_Pointer *)idris2_newReference(_anyPtr);
  retVal->onCollectFct = (Idris2_Closure *)_freeingFunction;
  return (Idris2_Value *)retVal;
}

Idris2_Value *
idris2_Prelude_IO_prim__onCollectAny(Idris2_Value *_anyPtr,
                                     Idris2_Value *_freeingFunction,
                                     Idris2_Value *_world) {
  Idris2_GCPointer *retVal = IDRIS2_NEW_VALUE(Idris2_GCPointer);
  retVal->header.tag = GC_POINTER_TAG;
  retVal->p = (Idris2_Pointer *)idris2_newReference(_anyPtr);
  retVal->onCollectFct = (Idris2_Closure *)_freeingFunction;
  return (Idris2_Value *)retVal;
}

// Threads

// %foreign "scheme:blodwen-mutex"
// prim__makeMutex : PrimIO Mutex
// using pthread_mutex_init(pthread_mutex_t *mutex, const pthread_mutexattr_t
// *attr)
Idris2_Value *System_Concurrency_Raw_prim__makeMutex(Idris2_Value *_world) {
  Idris2_Mutex *mut = IDRIS2_NEW_VALUE(Idris2_Mutex);
  mut->header.tag = MUTEX_TAG;
  mut->mutex = (pthread_mutex_t *)malloc(sizeof(pthread_mutex_t));
  int r = pthread_mutex_init(mut->mutex, NULL);
  IDRIS2_REFC_VERIFY(!r, "pthread_mutex_init failed: %s", strerror(r));
  return (Idris2_Value *)mut;
}

// %foreign "scheme:blodwen-lock"
// prim__mutexAcquire : Mutex -> PrimIO ()
// using pthread_mutex_lock(pthread_mutex_t *mutex)
Idris2_Value *System_Concurrency_Raw_prim__mutexAcquire(Idris2_Value *_mutex,
                                                        Idris2_Value *_world) {
  int r = pthread_mutex_lock(((Idris2_Mutex *)_mutex)->mutex);
  IDRIS2_REFC_VERIFY(!r, "pthread_mutex_lock failed: %s", strerror(r));
  return NULL;
}

// %foreign "scheme:blodwen-unlock"
// prim__mutexRelease : Mutex -> PrimIO ()
// using int pthread_mutex_unlock(pthread_mutex_t *mutex)
Idris2_Value *System_Concurrency_Raw_prim__mutexRelease(Idris2_Value *_mutex,
                                                        Idris2_Value *_world) {
  int r = pthread_mutex_unlock(((Idris2_Mutex *)_mutex)->mutex);
  IDRIS2_REFC_VERIFY(!r, "pthread_mutex_unlock failed: %s", strerror(r));
  return NULL;
}

// %foreign "scheme:blodwen-condition"
// prim__makeCondition : PrimIO Condition
// using int pthread_cond_init(pthread_cond_t *cond, const pthread_condattr_t
// *attr) with standard initialisation
Idris2_Value *System_Concurrency_Raw_prim__makeCondition(Idris2_Value *_world) {
  // typedef struct{
  //     Idris2_header header;
  //     pthread_cond_t *cond;
  // }Idris2_Condition;

  Idris2_Condition *c = IDRIS2_NEW_VALUE(Idris2_Condition);
  c->header.tag = CONDITION_TAG;
  c->cond = (pthread_cond_t *)malloc(sizeof(pthread_cond_t));
  IDRIS2_REFC_VERIFY(c->cond, "malloc failed");
  int r = pthread_cond_init(c->cond, NULL);
  IDRIS2_REFC_VERIFY(!r, "pthread_cond_init failed: %s", strerror(r));
  return (Idris2_Value *)c;
}

// %foreign "scheme:blodwen-condition-wait"
// prim__conditionWait : Condition -> Mutex -> PrimIO ()
// using int pthread_cond_wait(pthread_cond_t *, pthread_mutex_t *mutex)
Idris2_Value *System_Concurrency_Raw_prim__conditionWait(
    Idris2_Value *_condition, Idris2_Value *_mutex, Idris2_Value *_world) {
  Idris2_Condition *cond = (Idris2_Condition *)_condition;
  Idris2_Mutex *mutex = (Idris2_Mutex *)_mutex;
  int r = pthread_cond_wait(cond->cond, mutex->mutex);
  IDRIS2_REFC_VERIFY(!r, "pthread_cond_wait failed: %s", strerror(r));
  return NULL;
}

// %foreign "scheme:blodwen-condition-wait-timeout"
// prim__conditionWaitTimeout : Condition -> Mutex -> Int -> PrimIO ()
// using int pthread_cond_timedwait(pthread_cond_t *cond, pthread_mutex_t
// *mutex, const struct timespec *abstime)
Idris2_Value *System_Concurrency_Raw_prim__conditionWaitTimeout(
    Idris2_Value *_condition, Idris2_Value *_mutex, Idris2_Value *_timeout,
    Idris2_Value *_world) {
  Idris2_Condition *cond = (Idris2_Condition *)_condition;
  Idris2_Mutex *mutex = (Idris2_Mutex *)_mutex;
  int64_t timeout = idris2_vp_to_Int64(_timeout);
  struct timespec t;
  t.tv_sec = timeout / 1000000;
  t.tv_nsec = timeout % 1000000;
  int r = pthread_cond_timedwait(cond->cond, mutex->mutex, &t);
  IDRIS2_REFC_VERIFY(!r, "pthread_cond_timedwait failed: %s", strerror(r));
  return NULL;
}

// %foreign "scheme:blodwen-condition-signal"
// prim__conditionSignal : Condition -> PrimIO ()
// using int pthread_cond_signal(pthread_cond_t *cond)
Idris2_Value *
System_Concurrency_Raw_prim__conditionSignal(Idris2_Value *_condition,
                                             Idris2_Value *_world) {
  Idris2_Condition *cond = (Idris2_Condition *)_condition;
  int r = pthread_cond_signal(cond->cond);
  IDRIS2_REFC_VERIFY(!r, "pthread_cond_signal failed: %s", strerror(r));
  return NULL;
}

// %foreign "scheme:blodwen-condition-broadcast"
// prim__conditionBroadcast : Condition -> PrimIO ()
// using int pthread_cond_broadcast(pthread_cond_t *cond)
Idris2_Value *
System_Concurrency_Raw_prim__conditionBroadcast(Idris2_Value *_condition,
                                                Idris2_Value *_mutex) {
  Idris2_Condition *cond = (Idris2_Condition *)_condition;
  int r = pthread_cond_broadcast(cond->cond);
  IDRIS2_REFC_VERIFY(!r, "pthread_cond_broadcast failed: %s", strerror(r));
  return NULL;
}

char const idris2_constr_Int[] = "Int";
char const idris2_constr_Int8[] = "Int8";
char const idris2_constr_Int16[] = "Int16";
char const idris2_constr_Int32[] = "Int32";
char const idris2_constr_Int64[] = "Int64";
char const idris2_constr_Bits8[] = "Bits8";
char const idris2_constr_Bits16[] = "Bits16";
char const idris2_constr_Bits32[] = "Bits32";
char const idris2_constr_Bits64[] = "Bits64";
char const idris2_constr_Double[] = "Double";
char const idris2_constr_Integer[] = "Integer";
char const idris2_constr_Char[] = "Char";
char const idris2_constr_String[] = "String";
char const idris2_constr____gt[] = "->";
