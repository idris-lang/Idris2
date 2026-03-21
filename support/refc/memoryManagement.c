#include <stdbool.h>

#include "_datatypes.h"
#include "refc_util.h"
#include "runtime.h"

#if 0
struct {
  unsigned int n_newValue;
  unsigned int n_newReference;
  unsigned int n_actualNewReference;
  unsigned int n_immortalized;
  unsigned int n_removeReference;
  unsigned int n_tried_to_kill_immortals;
  unsigned int n_freed;
} idris2_memory_stat = {0, 0, 0, 0, 0, 00, 0};
#define IDRIS2_INC_MEMSTAT(x)                                                  \
  do {                                                                         \
    ++(idris2_memory_stat.x);                                                  \
  } while (0)

void idris2_dumpMemoryStats(void) {
  fprintf(
      stderr,
      "n_newValue = %u\n"
      "n_newReference = %u\n"
      "n_actualNewReference = %u\n"
      "n_immortalized = %u\n"
      "n_removeReference = %u\n"
      "n_tried_to_kill_immortals = %u\n"
      "n_freed = %u\n",
      idris2_memory_stat.n_newValue, idris2_memory_stat.n_newReference,
      idris2_memory_stat.n_actualNewReference,
      idris2_memory_stat.n_immortalized, idris2_memory_stat.n_removeReference,
      idris2_memory_stat.n_tried_to_kill_immortals, idris2_memory_stat.n_freed);
}

#else
#define IDRIS2_INC_MEMSTAT(x) ((void)0)
// don't inline this, Because IDRIS2_MEMSTAT works only at compiling support
// libraries to suppressing overhead.
void idris2_dumpMemoryStats(void) {}
#endif

Value *idris2_newValue(size_t size) {
  /* Try to get memory aligned to pointer-size. Prefer C11 aligned_alloc
     (not available on some platforms like older macOS), then posix_memalign,
     and finally fall back to malloc which typically returns pointer-aligned
     memory suitable for our needs. */
#if defined(__STDC_VERSION__) && (__STDC_VERSION__ >= 201112L) &&              \
    !defined(__APPLE__) && !defined(_WIN32)
  Value *retVal = (Value *)aligned_alloc(
      sizeof(void *),
      ((size + sizeof(void *) - 1) / sizeof(void *)) * sizeof(void *));
#elif ((defined(_POSIX_C_SOURCE) && (_POSIX_C_SOURCE >= 200112L)) ||           \
       (defined(_XOPEN_SOURCE) && (_XOPEN_SOURCE >= 600))) &&                  \
    !defined(_WIN32)
  Value *retVal = NULL;
  IDRIS2_REFC_VERIFY(
      posix_memalign((void **)&retVal, sizeof(void *),
                     ((size + sizeof(void *) - 1) / sizeof(void *)) *
                         sizeof(void *)) == 0,
      "posix_memalign failed");
#else
  Value *retVal = (Value *)IDRIS2_MALLOC(size);
#endif
  IDRIS2_REFC_VERIFY(retVal && !idris2_vp_is_unboxed(retVal), "malloc failed");
  IDRIS2_INC_MEMSTAT(n_newValue);
  retVal->header.refCounter = 1;
  retVal->header.tag = NO_TAG;
  retVal->header.reserved = 0; // colour=BLACK, buffered=false (clean state)
  return retVal;
}

Value_Constructor *idris2_newConstructor(int total, int tag) {
  Value_Constructor *retVal = (Value_Constructor *)idris2_newValue(
      sizeof(Value_Constructor) + sizeof(Value *) * total);
  retVal->header.tag = CONSTRUCTOR_TAG;
  retVal->total = total;
  retVal->tag = tag;
  retVal->name = NULL;
  return retVal;
}

Value_Closure *idris2_mkClosure(ClosureFun f, uint8_t arity, uint8_t filled) {
  Value_Closure *retVal = (Value_Closure *)idris2_newValue(
      sizeof(Value_Closure) + sizeof(Value *) * filled);
  retVal->header.tag = CLOSURE_TAG;
  retVal->f = f;
  retVal->arity = arity;
  retVal->filled = filled;
  return retVal; // caller must initialize args[].
}

Value *idris2_mkDouble(double d) {
  Value_Double *retVal = IDRIS2_NEW_VALUE(Value_Double);
  retVal->header.tag = DOUBLE_TAG;
  retVal->d = d;
  return (Value *)retVal;
}

Value *idris2_mkBits32_Boxed(uint32_t i) {
  Value_Bits32 *retVal = IDRIS2_NEW_VALUE(Value_Bits32);
  retVal->header.tag = BITS32_TAG;
  retVal->ui32 = i;
  return (Value *)retVal;
}

Value *idris2_mkBits64(uint64_t i) {
  if (i < 100)
    return (Value *)&idris2_predefined_Bits64[i];

  Value_Bits64 *retVal = IDRIS2_NEW_VALUE(Value_Bits64);
  retVal->header.tag = BITS64_TAG;
  retVal->ui64 = i;
  return (Value *)retVal;
}

Value *idris2_mkInt32_Boxed(int32_t i) {
  Value_Int32 *retVal = IDRIS2_NEW_VALUE(Value_Int32);
  retVal->header.tag = INT32_TAG;
  retVal->i32 = i;
  return (Value *)retVal;
}

Value *idris2_mkInt64(int64_t i) {
  if (i >= 0 && i < 100)
    return (Value *)&idris2_predefined_Int64[i];

  Value_Int64 *retVal = IDRIS2_NEW_VALUE(Value_Int64);
  retVal->header.tag = INT64_TAG;
  retVal->i64 = i;
  return (Value *)retVal;
}

Value_Integer *idris2_mkInteger(void) {
  Value_Integer *retVal = IDRIS2_NEW_VALUE(Value_Integer);
  retVal->header.tag = INTEGER_TAG;
#ifndef IDRIS2_NO_GMP
  mpz_init(retVal->i);
#else
  retVal->i = 0;
#endif
  return retVal;
}

Value *idris2_mkIntegerLiteral(char *i) {
  Value_Integer *retVal = idris2_mkInteger();
#ifndef IDRIS2_NO_GMP
  mpz_set_str(retVal->i, i, 10);
#else
  retVal->i = (int64_t)strtoll(i, NULL, 10);
#endif
  return (Value *)retVal;
}

Value_String *idris2_mkEmptyString(size_t l) {
  if (l == 1)
    return (Value_String *)&idris2_predefined_nullstring;

  Value_String *retVal = IDRIS2_NEW_VALUE(Value_String);
  retVal->header.tag = STRING_TAG;
  retVal->str = (char *)IDRIS2_MALLOC(l);
  memset(retVal->str, 0, l);
  return retVal;
}

Value_String *idris2_mkString(char *s) {
  if (s[0] == '\0')
    return (Value_String *)&idris2_predefined_nullstring;

  Value_String *retVal = IDRIS2_NEW_VALUE(Value_String);
  int l = strlen(s);
  retVal->header.tag = STRING_TAG;
  retVal->str = (char *)IDRIS2_MALLOC(l + 1);
  memset(retVal->str, 0, l + 1);
  memcpy(retVal->str, s, l);
  return retVal;
}

Value_Pointer *idris2_makePointer(void *ptr_Raw) {
  Value_Pointer *p = IDRIS2_NEW_VALUE(Value_Pointer);
  p->header.tag = POINTER_TAG;
  p->p = ptr_Raw;
  return p;
}

Value_GCPointer *idris2_makeGCPointer(void *ptr_Raw,
                                      Value_Closure *onCollectFct) {
  Value_GCPointer *p = IDRIS2_NEW_VALUE(Value_GCPointer);
  p->header.tag = GC_POINTER_TAG;
  p->p = idris2_makePointer(ptr_Raw);
  p->onCollectFct = onCollectFct;
  return p;
}

Value_Buffer *idris2_makeBuffer(void *buf) {
  Value_Buffer *b = IDRIS2_NEW_VALUE(Value_Buffer);
  b->header.tag = BUFFER_TAG;
  b->buffer = buf;
  return b;
}

Value_Array *idris2_makeArray(int length) {
  Value_Array *a = IDRIS2_NEW_VALUE(Value_Array);
  a->header.tag = ARRAY_TAG;
  a->capacity = length;
  a->arr = (Value **)IDRIS2_MALLOC(sizeof(Value *) * length);
  memset(a->arr, 0, sizeof(Value *) * length);
  return a;
}

Value *idris2_newReference(Value *source) {
  IDRIS2_INC_MEMSTAT(n_newReference);
  // note that we explicitly allow NULL as source (for erased arguments)
  if (source && !idris2_vp_is_unboxed(source) &&
      atomic_load_explicit(&source->header.refCounter, memory_order_relaxed) !=
          IDRIS2_VP_REFCOUNTER_MAX) {
    IDRIS2_INC_MEMSTAT(n_actualNewReference);
    uint16_t prev = atomic_fetch_add_explicit(&source->header.refCounter, 1,
                                              memory_order_relaxed);
    if (prev + 1 == IDRIS2_VP_REFCOUNTER_MAX)
      IDRIS2_INC_MEMSTAT(n_immortalized);
  }
  return source;
}

// ============================================================
// Bacon-Rajan trial-deletion cycle collector
// ============================================================
//
// The `reserved` byte in Value_header is repurposed for cycle-collector state:
//   bits 0-1: colour  (BLACK=0, GREY=1, WHITE=2, PURPLE=3)
//   bit  2:   buffered (object is in cc_roots[])
//
// Colours follow the Bacon-Rajan (2001) paper:
//   BLACK  - in use / known live
//   GREY   - being traced during trial deletion
//   WHITE  - confirmed garbage (all refs internal to cycle)
//   PURPLE - potential cycle root (refcount fell but did not reach 0)

#define CC_BLACK 0u
#define CC_GREY 1u
#define CC_WHITE 2u
#define CC_PURPLE 3u

#define CC_COLOUR_MASK 0x03u
#define CC_BUFFERED_BIT 0x04u

#define CC_GET_COLOUR(v) ((v)->header.reserved & CC_COLOUR_MASK)
#define CC_SET_COLOUR(v, c)                                                    \
  ((v)->header.reserved =                                                      \
       (uint8_t)(((v)->header.reserved & ~CC_COLOUR_MASK) | (c)))
#define CC_GET_BUFFERED(v) ((v)->header.reserved & CC_BUFFERED_BIT)
#define CC_SET_BUFFERED(v) ((v)->header.reserved |= CC_BUFFERED_BIT)
#define CC_CLR_BUFFERED(v) ((v)->header.reserved &= (uint8_t)~CC_BUFFERED_BIT)

/* Immortal values (refCounter == UINT16_MAX) may reside in read-only memory
 * (e.g. predefined constants in .rodata on macOS/arm64).  Any attempt to
 * atomically modify their refCounter causes EXC_BAD_ACCESS / Bus error.
 * These helpers perform the modification only for non-immortal values. */
#define CC_CHILD_DEC(c)                                                        \
  do {                                                                         \
    if (atomic_load_explicit(&(c)->header.refCounter, memory_order_relaxed) != \
        IDRIS2_VP_REFCOUNTER_MAX)                                              \
      atomic_fetch_sub_explicit(&(c)->header.refCounter, 1,                    \
                                memory_order_relaxed);                         \
  } while (0)
#define CC_CHILD_INC(c)                                                        \
  do {                                                                         \
    if (atomic_load_explicit(&(c)->header.refCounter, memory_order_relaxed) != \
        IDRIS2_VP_REFCOUNTER_MAX)                                              \
      atomic_fetch_add_explicit(&(c)->header.refCounter, 1,                    \
                                memory_order_relaxed);                         \
  } while (0)

// Trigger a collection run when this many roots have accumulated.
#define CC_ROOTS_THRESHOLD 256

static Value **cc_roots = NULL;
static size_t cc_roots_len = 0;
static size_t cc_roots_cap = 0;

/* Nesting depth of idris2_removeReference.  The cycle collector must only be
 * invoked at depth 1 (the outermost call), never from within a recursive free
 * traversal.  Triggering it mid-recursion lets markGrey trial-decrement
 * refcounts of objects that the ongoing recursion is still iterating over,
 * which corrupts the traversal and causes double-frees. */
static int idris2_removeRef_depth = 0;

static void cc_roots_push(Value *v) {
  if (cc_roots_len == cc_roots_cap) {
    cc_roots_cap = cc_roots_cap ? cc_roots_cap * 2 : 64;
    cc_roots =
        (Value **)IDRIS2_REALLOC(cc_roots, cc_roots_cap * sizeof(Value *));
    IDRIS2_REFC_VERIFY(cc_roots != NULL, "cc_roots realloc failed");
  }
  cc_roots[cc_roots_len++] = v;
}

// Only objects whose tag kind can contain Value* children can form cycles.
static bool cc_can_be_root(Value *v) {
  switch (v->header.tag) {
  case CLOSURE_TAG:
  case CONSTRUCTOR_TAG:
  case IOREF_TAG:
  case ARRAY_TAG:
  case GC_POINTER_TAG:
    return true;
  default:
    return false;
  }
}

// Called when an object's refcount was decremented but did not reach 0.
static void possibleCycleRoot(Value *v) {
  if (!cc_can_be_root(v))
    return;
  if (CC_GET_COLOUR(v) != CC_PURPLE) {
    CC_SET_COLOUR(v, CC_PURPLE);
    if (!CC_GET_BUFFERED(v)) {
      CC_SET_BUFFERED(v);
      cc_roots_push(v);
    }
  }
}

// ---- Phase 1: MarkGrey -------------------------------------------------
// Simulate trial deletion of all internal (intra-cycle) references by
// decrementing child refcounts and marking every reachable node grey.

static void markGrey(Value *v) {
  if (!v || idris2_vp_is_unboxed(v))
    return;
  if (v->header.refCounter == IDRIS2_VP_REFCOUNTER_MAX)
    return;
  if (CC_GET_COLOUR(v) == CC_GREY)
    return;
  CC_SET_COLOUR(v, CC_GREY);
  switch (v->header.tag) {
  case CLOSURE_TAG: {
    Value_Closure *cl = (Value_Closure *)v;
    for (int i = 0; i < cl->filled; i++) {
      Value *c = cl->args[i];
      if (!c || idris2_vp_is_unboxed(c))
        continue;
      CC_CHILD_DEC(c);
      markGrey(c);
    }
    break;
  }
  case CONSTRUCTOR_TAG: {
    Value_Constructor *co = (Value_Constructor *)v;
    for (int i = 0; i < co->total; i++) {
      Value *c = co->args[i];
      if (!c || idris2_vp_is_unboxed(c))
        continue;
      CC_CHILD_DEC(c);
      markGrey(c);
    }
    break;
  }
  case IOREF_TAG: {
    Value *c = ((Value_IORef *)v)->v;
    if (c && !idris2_vp_is_unboxed(c)) {
      CC_CHILD_DEC(c);
      markGrey(c);
    }
    break;
  }
  case ARRAY_TAG: {
    Value_Array *a = (Value_Array *)v;
    for (int i = 0; i < a->capacity; i++) {
      Value *c = a->arr[i];
      if (!c || idris2_vp_is_unboxed(c))
        continue;
      CC_CHILD_DEC(c);
      markGrey(c);
    }
    break;
  }
  case GC_POINTER_TAG: {
    Value_GCPointer *gcp = (Value_GCPointer *)v;
    if (gcp->p) {
      CC_CHILD_DEC((Value *)gcp->p);
      markGrey((Value *)gcp->p);
    }
    if (gcp->onCollectFct) {
      CC_CHILD_DEC((Value *)gcp->onCollectFct);
      markGrey((Value *)gcp->onCollectFct);
    }
    break;
  }
  default:
    break;
  }
}

// ---- Phase 2a: ScanBlack -----------------------------------------------
// Restore refcounts for objects that are still externally referenced.

static void scanBlack(Value *v) {
  if (!v || idris2_vp_is_unboxed(v))
    return;
  if (v->header.refCounter == IDRIS2_VP_REFCOUNTER_MAX)
    return;
  CC_SET_COLOUR(v, CC_BLACK);
  switch (v->header.tag) {
  case CLOSURE_TAG: {
    Value_Closure *cl = (Value_Closure *)v;
    for (int i = 0; i < cl->filled; i++) {
      Value *c = cl->args[i];
      if (!c || idris2_vp_is_unboxed(c))
        continue;
      CC_CHILD_INC(c);
      if (CC_GET_COLOUR(c) != CC_BLACK)
        scanBlack(c);
    }
    break;
  }
  case CONSTRUCTOR_TAG: {
    Value_Constructor *co = (Value_Constructor *)v;
    for (int i = 0; i < co->total; i++) {
      Value *c = co->args[i];
      if (!c || idris2_vp_is_unboxed(c))
        continue;
      CC_CHILD_INC(c);
      if (CC_GET_COLOUR(c) != CC_BLACK)
        scanBlack(c);
    }
    break;
  }
  case IOREF_TAG: {
    Value *c = ((Value_IORef *)v)->v;
    if (c && !idris2_vp_is_unboxed(c)) {
      CC_CHILD_INC(c);
      if (CC_GET_COLOUR(c) != CC_BLACK)
        scanBlack(c);
    }
    break;
  }
  case ARRAY_TAG: {
    Value_Array *a = (Value_Array *)v;
    for (int i = 0; i < a->capacity; i++) {
      Value *c = a->arr[i];
      if (!c || idris2_vp_is_unboxed(c))
        continue;
      CC_CHILD_INC(c);
      if (CC_GET_COLOUR(c) != CC_BLACK)
        scanBlack(c);
    }
    break;
  }
  case GC_POINTER_TAG: {
    Value_GCPointer *gcp = (Value_GCPointer *)v;
    if (gcp->p) {
      CC_CHILD_INC((Value *)gcp->p);
      if (CC_GET_COLOUR((Value *)gcp->p) != CC_BLACK)
        scanBlack((Value *)gcp->p);
    }
    if (gcp->onCollectFct) {
      CC_CHILD_INC((Value *)gcp->onCollectFct);
      if (CC_GET_COLOUR((Value *)gcp->onCollectFct) != CC_BLACK)
        scanBlack((Value *)gcp->onCollectFct);
    }
    break;
  }
  default:
    break;
  }
}

// ---- Phase 2: Scan -----------------------------------------------------
// Mark WHITE nodes whose refcount stayed at 0 (garbage); restore live ones.

static void scan(Value *v) {
  if (!v || idris2_vp_is_unboxed(v))
    return;
  if (CC_GET_COLOUR(v) != CC_GREY)
    return;
  if (atomic_load_explicit(&v->header.refCounter, memory_order_relaxed) > 0) {
    scanBlack(v);
  } else {
    CC_SET_COLOUR(v, CC_WHITE);
    switch (v->header.tag) {
    case CLOSURE_TAG: {
      Value_Closure *cl = (Value_Closure *)v;
      for (int i = 0; i < cl->filled; i++)
        scan(cl->args[i]);
      break;
    }
    case CONSTRUCTOR_TAG: {
      Value_Constructor *co = (Value_Constructor *)v;
      for (int i = 0; i < co->total; i++)
        scan(co->args[i]);
      break;
    }
    case IOREF_TAG:
      scan(((Value_IORef *)v)->v);
      break;
    case ARRAY_TAG: {
      Value_Array *a = (Value_Array *)v;
      for (int i = 0; i < a->capacity; i++)
        scan(a->arr[i]);
      break;
    }
    case GC_POINTER_TAG: {
      Value_GCPointer *gcp = (Value_GCPointer *)v;
      scan((Value *)gcp->p);
      scan((Value *)gcp->onCollectFct);
      break;
    }
    default:
      break;
    }
  }
}

// ---- Phase 3: CollectWhite ---------------------------------------------

// Free non-Value internal resources of v, then free(v) itself.
// Children have already been freed by the collectWhite recursion.
static void freeValueDirect(Value *v) {
  switch (v->header.tag) {
  case INTEGER_TAG:
#ifndef IDRIS2_NO_GMP
    mpz_clear(((Value_Integer *)v)->i);
#endif
    break;
  case STRING_TAG:
    IDRIS2_FREE(((Value_String *)v)->str);
    break;
  case BUFFER_TAG:
    IDRIS2_FREE(((Value_Buffer *)v)->buffer);
    break;
  case ARRAY_TAG:
    // arr entries were freed by the collectWhite recursion; free the array
    // itself.
    IDRIS2_FREE(((Value_Array *)v)->arr);
    break;
#ifndef IDRIS2_NO_THREADS
  case MUTEX_TAG: {
    Value_Mutex *m = (Value_Mutex *)v;
    pthread_mutex_destroy(m->mutex);
    IDRIS2_FREE(m->mutex);
    break;
  }
  case CONDITION_TAG: {
    Value_Condition *c = (Value_Condition *)v;
    pthread_cond_destroy(c->cond);
    IDRIS2_FREE(c->cond);
    break;
  }
  case SEMAPHORE_TAG: {
    Value_Semaphore *s = (Value_Semaphore *)v;
    pthread_cond_destroy(&s->cond);
    pthread_mutex_destroy(&s->mutex);
    break;
  }
  case BARRIER_TAG: {
    Value_Barrier *b = (Value_Barrier *)v;
    pthread_cond_destroy(&b->cond);
    pthread_mutex_destroy(&b->mutex);
    break;
  }
#endif /* IDRIS2_NO_THREADS */
  default:
    break;
  }
  IDRIS2_FREE(v);
}

static void collectWhite(Value *v) {
  if (!v || idris2_vp_is_unboxed(v))
    return;
  if (CC_GET_COLOUR(v) != CC_WHITE || CC_GET_BUFFERED(v))
    return;
  CC_SET_COLOUR(v, CC_BLACK); // prevent re-entry

  // For GC_POINTER, invoke the finalizer before children are freed.
  if (v->header.tag == GC_POINTER_TAG) {
    Value_GCPointer *gcp = (Value_GCPointer *)v;
    Value *c1 =
        idris2_apply_closure((Value *)gcp->onCollectFct, (Value *)gcp->p);
    idris2_apply_closure(c1, NULL);
  }

  switch (v->header.tag) {
  case CLOSURE_TAG: {
    Value_Closure *cl = (Value_Closure *)v;
    for (int i = 0; i < cl->filled; i++)
      collectWhite(cl->args[i]);
    break;
  }
  case CONSTRUCTOR_TAG: {
    Value_Constructor *co = (Value_Constructor *)v;
    for (int i = 0; i < co->total; i++)
      collectWhite(co->args[i]);
    break;
  }
  case IOREF_TAG:
    collectWhite(((Value_IORef *)v)->v);
    break;
  case ARRAY_TAG: {
    Value_Array *a = (Value_Array *)v;
    for (int i = 0; i < a->capacity; i++)
      collectWhite(a->arr[i]);
    break;
  }
  case GC_POINTER_TAG: {
    Value_GCPointer *gcp = (Value_GCPointer *)v;
    collectWhite((Value *)gcp->p);
    collectWhite((Value *)gcp->onCollectFct);
    break;
  }
  default:
    break;
  }

  freeValueDirect(v);
}

// ---- cc_roots bookkeeping helpers -------------------------------------

// Remove v from cc_roots if it is currently buffered there.
// Call this before directly free()-ing a Value that bypasses
// idris2_removeReference (e.g. the fast paths in idris2_trampoline /
// idris2_tailcall_apply_closure).
void idris2_cc_remove_if_buffered(Value *v) {
  if (!v || idris2_vp_is_unboxed(v) || !CC_GET_BUFFERED(v))
    return;
  for (size_t i = 0; i < cc_roots_len; i++) {
    if (cc_roots[i] == v) {
      cc_roots[i] = cc_roots[cc_roots_len - 1];
      cc_roots_len--;
      break;
    }
  }
  CC_CLR_BUFFERED(v);
}

// ---- Main entry point --------------------------------------------------

void idris2_collectCycles(void) {
  if (cc_roots_len == 0)
    return;

  // Phase 1 (MarkRoots + MarkGrey):
  //   - PURPLE roots: begin trial deletion via markGrey.
  //   - GREY roots: already visited by markGrey() as a child of another root
  //     in this same pass.  Leave them in cc_roots so Phase 2 (scan) can
  //     inspect their trial-decremented refcount and either restore them via
  //     scanBlack or mark them WHITE for collection.  Do NOT free them here —
  //     their rc was decremented by the parent's markGrey traversal and may
  //     still be restored to > 0 by a subsequent scanBlack call.
  //   - All other colours (BLACK/WHITE): stale entry — the object was already
  //     removed from cc_roots and freed by removeReference when its rc reached
  //     0.  This branch should be unreachable now, but guard it defensively.
  for (size_t i = 0; i < cc_roots_len; i++) {
    Value *v = cc_roots[i];
    if (CC_GET_COLOUR(v) == CC_PURPLE) {
      markGrey(v);
    }
    // GREY: leave in cc_roots for Phase 2 scan() to handle.
    // (BLACK/WHITE entries are removed by removeReference before they get
    // here.)
  }

  // Phase 2 (Scan): restore live objects, mark confirmed garbage WHITE.
  for (size_t i = 0; i < cc_roots_len; i++) {
    if (cc_roots[i])
      scan(cc_roots[i]);
  }

  // Phase 3 (CollectRoots/CollectWhite): free garbage cycles.
  // Swap out the roots array first so that possibleCycleRoot calls from
  // finalizers (during CollectWhite) go to a fresh list.
  size_t old_len = cc_roots_len;
  Value **old_roots = cc_roots;
  cc_roots = NULL;
  cc_roots_len = 0;
  cc_roots_cap = 0;

  for (size_t i = 0; i < old_len; i++) {
    Value *v = old_roots[i];
    CC_CLR_BUFFERED(v); // must clear before collectWhite checks it
    collectWhite(v);
  }
  IDRIS2_FREE(old_roots);
}

void idris2_removeReference(Value *elem) {
  IDRIS2_INC_MEMSTAT(n_removeReference);
  if (!elem || idris2_vp_is_unboxed(elem))
    return;
  else if (atomic_load_explicit(&elem->header.refCounter,
                                memory_order_relaxed) ==
           IDRIS2_VP_REFCOUNTER_MAX) {
    IDRIS2_INC_MEMSTAT(n_tried_to_kill_immortals);
    return;
  } else if (atomic_fetch_sub_explicit(&elem->header.refCounter, 1,
                                       memory_order_acq_rel) != 1) {
    possibleCycleRoot(elem);
    /* Only trigger the cycle collector at the outermost removeReference call.
     * Triggering it mid-recursion lets markGrey trial-decrement refcounts of
     * objects that the ongoing recursive free is still iterating over, leading
     * to double-frees and use-after-free errors. */
    if (cc_roots_len >= CC_ROOTS_THRESHOLD && idris2_removeRef_depth == 0)
      idris2_collectCycles();
    return;
  } else {
    idris2_removeRef_depth++;
    IDRIS2_INC_MEMSTAT(n_freed);
    switch (elem->header.tag) {
    case BITS32_TAG:
    case BITS64_TAG:
    case INT32_TAG:
    case INT64_TAG:
      /* nothing to delete, added for sake of completeness */
      break;
    case INTEGER_TAG:
#ifndef IDRIS2_NO_GMP
      mpz_clear(((Value_Integer *)elem)->i);
#endif
      break;

    case DOUBLE_TAG:
      /* nothing to delete, added for sake of completeness */
      break;

    case STRING_TAG:
      IDRIS2_FREE(((Value_String *)elem)->str);
      break;

    case CLOSURE_TAG: {
      Value_Closure *cl = (Value_Closure *)elem;
      for (int i = 0; i < cl->filled; ++i)
        idris2_removeReference(cl->args[i]);
      break;
    }

    case CONSTRUCTOR_TAG: {
      Value_Constructor *constr = (Value_Constructor *)elem;
      for (int i = 0; i < constr->total; i++) {
        idris2_removeReference(constr->args[i]);
      }
      break;
    }
    case IOREF_TAG:
      idris2_removeReference(((Value_IORef *)elem)->v);
      break;

    case BUFFER_TAG: {
      Value_Buffer *b = (Value_Buffer *)elem;
      IDRIS2_FREE(b->buffer);
      break;
    }

    case ARRAY_TAG: {
      Value_Array *a = (Value_Array *)elem;
      for (int i = 0; i < a->capacity; i++) {
        idris2_removeReference(a->arr[i]);
      }
      IDRIS2_FREE(a->arr);
      break;
    }
    case POINTER_TAG:
      /* nothing to delete, added for sake of completeness */
      break;

    case GC_POINTER_TAG: {
      /* maybe here we need to invoke onCollectAny */
      Value_GCPointer *vPtr = (Value_GCPointer *)elem;
      Value *closure1 =
          idris2_apply_closure((Value *)vPtr->onCollectFct, (Value *)vPtr->p);
      idris2_apply_closure(closure1, NULL);
      idris2_removeReference((Value *)vPtr->p);
      break;
    }

#ifndef IDRIS2_NO_THREADS
    case MUTEX_TAG: {
      Value_Mutex *m = (Value_Mutex *)elem;
      pthread_mutex_destroy(m->mutex);
      IDRIS2_FREE(m->mutex);
      break;
    }

    case CONDITION_TAG: {
      Value_Condition *c = (Value_Condition *)elem;
      pthread_cond_destroy(c->cond);
      IDRIS2_FREE(c->cond);
      break;
    }

    case THREAD_TAG:
      /* pthread_t is embedded by value; nothing extra to free. */
      break;

    case SEMAPHORE_TAG: {
      Value_Semaphore *s = (Value_Semaphore *)elem;
      pthread_cond_destroy(&s->cond);
      pthread_mutex_destroy(&s->mutex);
      break;
    }

    case BARRIER_TAG: {
      Value_Barrier *b = (Value_Barrier *)elem;
      pthread_cond_destroy(&b->cond);
      pthread_mutex_destroy(&b->mutex);
      break;
    }
#endif /* IDRIS2_NO_THREADS */

    default:
      break;
    }
    // If this object is in cc_roots (buffered), remove it first so the
    // cycle collector doesn't see a dangling pointer.
    idris2_cc_remove_if_buffered(elem);
    IDRIS2_FREE(elem);
    idris2_removeRef_depth--;
    /* Now that we've fully unwound to the outermost call, run any deferred
     * cycle collection that was held back to avoid mid-recursion corruption. */
    if (idris2_removeRef_depth == 0 && cc_roots_len >= CC_ROOTS_THRESHOLD)
      idris2_collectCycles();
  }
}

// /////////////////////////////////////////////////////////////////////////
// PRE-DEFINED VLAUES

#define IDRIS2_MK_PREDEFINED_INT_10(t, n)                                      \
  {IDRIS2_STOCKVAL(t), (n + 0)}, {IDRIS2_STOCKVAL(t), (n + 1)},                \
      {IDRIS2_STOCKVAL(t), (n + 2)}, {IDRIS2_STOCKVAL(t), (n + 3)},            \
      {IDRIS2_STOCKVAL(t), (n + 4)}, {IDRIS2_STOCKVAL(t), (n + 5)},            \
      {IDRIS2_STOCKVAL(t), (n + 6)}, {IDRIS2_STOCKVAL(t), (n + 7)},            \
      {IDRIS2_STOCKVAL(t), (n + 8)}, {                                         \
    IDRIS2_STOCKVAL(t), (n + 9)                                                \
  }
Value_Int64 const idris2_predefined_Int64[100] = {
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 0),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 10),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 20),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 30),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 40),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 50),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 60),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 70),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 80),
    IDRIS2_MK_PREDEFINED_INT_10(INT64_TAG, 90)};

Value_Bits64 const idris2_predefined_Bits64[100] = {
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 0),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 10),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 20),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 30),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 40),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 50),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 60),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 70),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 80),
    IDRIS2_MK_PREDEFINED_INT_10(BITS64_TAG, 90)};

Value_String const idris2_predefined_nullstring = {IDRIS2_STOCKVAL(STRING_TAG),
                                                   ""};

static bool idris2_predefined_integer_initialized = false;
Value_Integer idris2_predefined_Integer[100];

Value *idris2_getPredefinedInteger(int n) {
  IDRIS2_REFC_VERIFY(n >= 0 && n < 100,
                     "invalid range of predefined integers.");

  if (!idris2_predefined_integer_initialized) {
    idris2_predefined_integer_initialized = true;
    for (int i = 0; i < 100; ++i) {
      idris2_predefined_Integer[i].header.refCounter = IDRIS2_VP_REFCOUNTER_MAX;
      idris2_predefined_Integer[i].header.tag = INTEGER_TAG;
      idris2_predefined_Integer[i].header.reserved = 0;
#ifndef IDRIS2_NO_GMP
      mpz_init(idris2_predefined_Integer[i].i);
      mpz_set_si(idris2_predefined_Integer[i].i, i);
#else
      idris2_predefined_Integer[i].i = (int64_t)i;
#endif
    }
  }
  return (Value *)&idris2_predefined_Integer[n];
}
