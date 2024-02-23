#include "prim.h"
#include "refc_util.h"
#include <string.h>
#include <unistd.h>

Value *idris2_Data_IORef_prim__newIORef(Value *erased, Value *input_value,
                                        Value *_world) {
  Value_IORef *ioRef = IDRIS2_NEW_VALUE(Value_IORef);
  ioRef->header.tag = IOREF_TAG;
  ioRef->v = newReference(input_value);
  return (Value *)ioRef;
}

Value *idris2_Data_IORef_prim__writeIORef(Value *erased, Value *_ioref,
                                          Value *new_value, Value *_world) {
  Value_IORef *ioref = (Value_IORef *)_ioref;
  newReference(new_value);
  Value *old = ioref->v;
  ioref->v = new_value;
  removeReference(old);
  return NULL;
}

// -----------------------------------
//       System operations
// -----------------------------------

static Value *osstring = NULL;

Value *idris2_System_Info_prim__os(void) {
  if (osstring == NULL) {
    osstring = (Value *)makeString(
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
    );
  }
  return newReference(osstring);
}

// NOTE: The codegen is obviously determined at compile time,
//       so the backend should optimize it by replacing it with a constant.
//       It would probably also be useful for conditional compilation.
static Value *codegenstring = NULL;

Value *idris2_System_Info_prim__codegen(void) {
  if (codegenstring == NULL)
    codegenstring = (Value *)makeString("refc");
  return newReference(codegenstring);
}

Value *idris2_crash(Value *msg) {
  Value_String *str = (Value_String *)msg;
  printf("ERROR: %s\n", str->str);
  exit(-1);
}

//
//
//
// // -----------------------------------
// //         Array operations
// // -----------------------------------

Value *idris2_Data_IOArray_Prims_prim__newArray(Value *erased, Value *_length,
                                                Value *v, Value *_word) {
  int length = extractInt(_length);
  Value_Array *a = makeArray(length);

  for (int i = 0; i < length; i++) {
    a->arr[i] = newReference(v);
  }

  return (Value *)a;
}

Value *idris2_Data_IOArray_Prims_prim__arraySet(Value *erased, Value *_array,
                                                Value *_index, Value *v,
                                                Value *_word) {
  Value_Array *a = (Value_Array *)_array;
  removeReference(a->arr[((Value_Int64 *)_index)->i64]);
  a->arr[((Value_Int64 *)_index)->i64] = newReference(v);
  return NULL;
}

//
// -----------------------------------
//      Pointer operations
// -----------------------------------

Value *idris2_Prelude_IO_prim__onCollect(Value *_erased, Value *_anyPtr,
                                         Value *_freeingFunction,
                                         Value *_world) {
  Value_GCPointer *retVal = IDRIS2_NEW_VALUE(Value_GCPointer);
  retVal->header.tag = GC_POINTER_TAG;
  retVal->p = (Value_Pointer *)newReference(_anyPtr);
  retVal->onCollectFct = (Value_Closure *)_freeingFunction;
  return (Value *)retVal;
}

Value *idris2_Prelude_IO_prim__onCollectAny(Value *_anyPtr,
                                            Value *_freeingFunction,
                                            Value *_world) {
  Value_GCPointer *retVal = IDRIS2_NEW_VALUE(Value_GCPointer);
  retVal->header.tag = GC_POINTER_TAG;
  retVal->p = (Value_Pointer *)newReference(_anyPtr);
  retVal->onCollectFct = (Value_Closure *)_freeingFunction;
  return (Value *)retVal;
}

// Threads

// %foreign "scheme:blodwen-mutex"
// prim__makeMutex : PrimIO Mutex
// using pthread_mutex_init(pthread_mutex_t *mutex, const pthread_mutexattr_t
// *attr)
Value *System_Concurrency_Raw_prim__makeMutex(Value *_world) {
  Value_Mutex *mut = IDRIS2_NEW_VALUE(Value_Mutex);
  mut->header.tag = MUTEX_TAG;
  mut->mutex = (pthread_mutex_t *)malloc(sizeof(pthread_mutex_t));
  int r = pthread_mutex_init(mut->mutex, NULL);
  IDRIS2_REFC_VERIFY(!r, "pthread_mutex_init failed: %s", strerror(r));
  return (Value *)mut;
}

// %foreign "scheme:blodwen-lock"
// prim__mutexAcquire : Mutex -> PrimIO ()
// using pthread_mutex_lock(pthread_mutex_t *mutex)
Value *System_Concurrency_Raw_prim__mutexAcquire(Value *_mutex, Value *_world) {
  int r = pthread_mutex_lock(((Value_Mutex *)_mutex)->mutex);
  IDRIS2_REFC_VERIFY(!r, "pthread_mutex_lock failed: %s", strerror(r));
  return NULL;
}

// %foreign "scheme:blodwen-unlock"
// prim__mutexRelease : Mutex -> PrimIO ()
// using int pthread_mutex_unlock(pthread_mutex_t *mutex)
Value *System_Concurrency_Raw_prim__mutexRelease(Value *_mutex, Value *_world) {
  int r = pthread_mutex_unlock(((Value_Mutex *)_mutex)->mutex);
  IDRIS2_REFC_VERIFY(!r, "pthread_mutex_unlock failed: %s", strerror(r));
  return NULL;
}

// %foreign "scheme:blodwen-condition"
// prim__makeCondition : PrimIO Condition
// using int pthread_cond_init(pthread_cond_t *cond, const pthread_condattr_t
// *attr) with standard initialisation
Value *System_Concurrency_Raw_prim__makeCondition(Value *_world) {
  // typedef struct{
  //     Value_header header;
  //     pthread_cond_t *cond;
  // }Value_Condition;

  Value_Condition *c = IDRIS2_NEW_VALUE(Value_Condition);
  c->header.tag = CONDITION_TAG;
  c->cond = (pthread_cond_t *)malloc(sizeof(pthread_cond_t));
  IDRIS2_REFC_VERIFY(c->cond, "malloc failed");
  int r = pthread_cond_init(c->cond, NULL);
  IDRIS2_REFC_VERIFY(!r, "pthread_cond_init failed: %s", strerror(r));
  return (Value *)c;
}

// %foreign "scheme:blodwen-condition-wait"
// prim__conditionWait : Condition -> Mutex -> PrimIO ()
// using int pthread_cond_wait(pthread_cond_t *, pthread_mutex_t *mutex)
Value *System_Concurrency_Raw_prim__conditionWait(Value *_condition,
                                                  Value *_mutex,
                                                  Value *_world) {
  Value_Condition *cond = (Value_Condition *)_condition;
  Value_Mutex *mutex = (Value_Mutex *)_mutex;
  int r = pthread_cond_wait(cond->cond, mutex->mutex);
  IDRIS2_REFC_VERIFY(!r, "pthread_cond_wait failed: %s", strerror(r));
  return NULL;
}

// %foreign "scheme:blodwen-condition-wait-timeout"
// prim__conditionWaitTimeout : Condition -> Mutex -> Int -> PrimIO ()
// using int pthread_cond_timedwait(pthread_cond_t *cond, pthread_mutex_t
// *mutex, const struct timespec *abstime)
Value *System_Concurrency_Raw_prim__conditionWaitTimeout(Value *_condition,
                                                         Value *_mutex,
                                                         Value *_timeout,
                                                         Value *_world) {
  Value_Condition *cond = (Value_Condition *)_condition;
  Value_Mutex *mutex = (Value_Mutex *)_mutex;
  Value_Int64 *timeout = (Value_Int64 *)_timeout;
  struct timespec t;
  t.tv_sec = timeout->i64 / 1000000;
  t.tv_nsec = timeout->i64 % 1000000;
  int r = pthread_cond_timedwait(cond->cond, mutex->mutex, &t);
  IDRIS2_REFC_VERIFY(!r, "pthread_cond_timedwait failed: %s", strerror(r));
  return NULL;
}

// %foreign "scheme:blodwen-condition-signal"
// prim__conditionSignal : Condition -> PrimIO ()
// using int pthread_cond_signal(pthread_cond_t *cond)
Value *System_Concurrency_Raw_prim__conditionSignal(Value *_condition,
                                                    Value *_world) {
  Value_Condition *cond = (Value_Condition *)_condition;
  int r = pthread_cond_signal(cond->cond);
  IDRIS2_REFC_VERIFY(!r, "pthread_cond_signal failed: %s", strerror(r));
  return NULL;
}

// %foreign "scheme:blodwen-condition-broadcast"
// prim__conditionBroadcast : Condition -> PrimIO ()
// using int pthread_cond_broadcast(pthread_cond_t *cond)
Value *System_Concurrency_Raw_prim__conditionBroadcast(Value *_condition,
                                                       Value *_mutex) {
  Value_Condition *cond = (Value_Condition *)_condition;
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
