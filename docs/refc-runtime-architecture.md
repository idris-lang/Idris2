# RefC Runtime: Value Representation and Architecture

A guide to the in-memory value representation used by the Idris 2 RefC
(reference-counted C) backend. This is the primary reference for anyone
working on the runtime, writing C FFI bindings, or debugging generated code.

Source files: `support/refc/`

---

## 1. The `Value` Type

Every Idris value at runtime is represented as a pointer to a `Value`:

```c
typedef struct {
  uint16_t refCounter;   // reference count (0 = static/stack-allocated)
  uint16_t tag;          // discriminator — see tags below
} Value_header;

typedef struct {
  Value_header header;
} Value;
```

All concrete value types embed `Value_header` as their first member,
so any `Value *` can safely be cast to the appropriate concrete type
once the `tag` field has been inspected.

**Reference counter semantics:**

- `refCounter == 0` — the value is *static* (never freed). Used for
  compile-time constants such as string literals and predefined integers.
- `refCounter == 1` — the value is *unique* (owned by exactly one slot).
  The runtime can mutate or free it directly; this is the fast path.
- `refCounter > 1` — the value is *shared*. Mutations must copy-on-write;
  frees only decrement the counter.

---

## 2. Tag Values

Defined in `_datatypes.h`:

| Tag constant        | Value | Concrete type          | Description                         |
|---------------------|------:|------------------------|-------------------------------------|
| `OBJECT_TAG`        |     0 | `Value_Constructor`    | Algebraic data type constructor     |
| `INT_TAG`           |     1 | *(unboxed — see §3)*   | Small `Int` (pointer-tagged)        |
| `DOUBLE_TAG`        |     2 | `Value_Double`         | IEEE 754 double                     |
| `STRING_TAG`        |     3 | `Value_String`         | NUL-terminated UTF-8 string         |
| `CLOSURE_TAG`       |     5 | `Value_Closure`        | Partially or fully applied function |
| `BITS32_TAG`        |     7 | `Value_Bits32`         | 32-bit unsigned integer             |
| `BITS64_TAG`        |     8 | `Value_Bits64`         | 64-bit unsigned integer             |
| `INTEGER_TAG`       |     9 | `Value_Integer`        | Arbitrary-precision integer (GMP)   |
| `IOREF_TAG`         |    10 | `Value_IORef`          | Mutable reference (`IORef a`)       |
| `ARRAY_TAG`         |    11 | `Value_Array`          | Mutable array (`IOArray a`)         |
| `POINTER_TAG`       |    12 | `Value_Pointer`        | Raw C pointer                       |
| `GC_POINTER_TAG`    |    13 | `Value_GCPointer`      | GC-managed pointer with finaliser   |
| `BUFFER_TAG`        |    14 | `Value_Buffer`         | Byte buffer                         |
| `MUTEX_TAG`         |    15 | `Value_Mutex`          | `pthread_mutex_t` wrapper           |
| `CONDITION_TAG`     |    16 | `Value_Condition`      | `pthread_cond_t` wrapper            |
| `THREAD_TAG`        |    17 | `Value_Thread`         | `pthread_t` wrapper                 |
| `INT8_TAG`          |    18 | *(unboxed)*            | 8-bit signed integer                |
| `INT16_TAG`         |    19 | *(unboxed)*            | 16-bit signed integer               |
| `INT32_TAG`         |    20 | `Value_Int32`          | 32-bit signed integer               |
| `INT64_TAG`         |    21 | `Value_Int64`          | 64-bit signed integer               |
| `CLOSURE_TAG`       |     5 | `Value_Closure`        | see above                           |

Constructor tags (`OBJECT_TAG`) double as constructor discriminators:
the `tag` field of a `Value_Constructor` holds the constructor index
(or `-1` for constructor-by-name matching).

---

## 3. Unboxed Values

Small integers (`Int`, `Int8`, `Int16`) and `Char` are stored unboxed
as tagged pointer values — no heap allocation is needed:

```c
// Pack an integer into a pointer (low bit set = unboxed)
#define idris2_mkIntegral(x) \
    ((Value *)(((uintptr_t)(x) << idris2_vp_int_shift) | 1))

// Unpack
#define idris2_vp_is_unboxed(p)  ((uintptr_t)(p) & 1)
#define idris2_vp_to_Int64(p)    ((int64_t)((uintptr_t)(p) >> idris2_vp_int_shift))
```

The bottom bit being set is the "unboxed" sentinel; the remaining bits
hold the integer value. On 64-bit systems `idris2_vp_int_shift = 1`,
giving a 63-bit signed range.

---

## 4. Concrete Types

### `Value_Constructor` (algebraic data)

```c
typedef struct {
  Value_header header;   // tag = OBJECT_TAG; header.tag = constructor index
  char *name;            // constructor name (for name-based matching)
  size_t total;          // total number of fields
  Value *args[];         // flexible array of fields
} Value_Constructor;
```

Constructor `NULL` represents `Nothing`, `Nil`, `False`, `Z`, and `()`.

### `Value_Closure`

```c
typedef struct {
  Value_header header;   // tag = CLOSURE_TAG
  void *f;               // function pointer (cast to FUNn or FUNStar)
  size_t arity;          // total expected args
  size_t filled;         // args already captured
  Value *args[];         // captured arguments
} Value_Closure;
```

A closure is *saturated* when `filled == arity`. The trampoline
(`idris2_trampoline`) dispatches saturated closures in a loop to
implement tail-call optimisation without growing the C stack.

### `Value_String`

```c
typedef struct {
  Value_header header;   // tag = STRING_TAG
  char str[];            // flexible array — inline NUL-terminated string
} Value_String;
```

String bytes are stored inline (no separate heap allocation). The
current implementation is byte-based; Unicode code-point awareness
is tracked in Task 1 of `REFC_BACKEND_TASKS.md`.

---

## 5. The Trampoline and Tail-Call Optimisation

Direct tail calls in Idris are compiled to *return a saturated closure*
rather than making a recursive C call. The outermost `idris2_trampoline`
loop then dispatches the closure without adding a C stack frame:

```c
Value *idris2_trampoline(Value *it) {
  while (it && !idris2_vp_is_unboxed(it) && it->header.tag == CLOSURE_TAG) {
    Value_Closure *clos = (Value_Closure *)it;
    if (clos->filled < clos->arity) break;
    it = idris2_dispatch_closure(clos);
    ...
  }
  return it;
}
```

`idris2_dispatch_closure` uses a `switch` on `arity` to call the
underlying C function with individual arguments (FUN0–FUN16) or as a
`Value **` array (FUNStar for arity > 16). Both paths are stack-safe.

**Mutual recursion** is also handled transparently: when function A
tail-calls B, it returns a closure for B; the trampoline dispatches B,
which may return a closure for A, and so on — all in the same loop
iteration with O(1) C stack depth.

---

## 6. Memory Management Lifecycle

```text
Allocation   idris2_newConstructor / idris2_mkClosure / IDRIS2_NEW_VALUE
                 refCounter = 1

Share        idris2_newReference(v)
                 refCounter++; return v

Release      idris2_removeReference(v)
                 if --refCounter == 0: free fields recursively, free v

Unique test  idris2_isUnique(v)
                 returns true when refCounter == 1
                 (optimises mutations and closure dispatch)
```

`idris2_isUnique` enables several optimisations:

- In `idris2_tailcall_apply_closure`: if the closure is unique, its
  args are moved (no `newReference`); otherwise args are copied with
  `newReference`.
- Constructor reuse (`IDRIS2_REUSE`): if a scrutinised constructor is
  unique, its allocation can be recycled for the result.

---

## 7. Static Values

Values with `refCounter == 0` are never freed. These are used for:

- Compile-time string constants (`IDRIS2_STOCKVAL`)
- Predefined small integers (`idris2_predefined_Int64`)
- Predefined constructors for `True`, `False`, `Nothing`, etc.

`idris2_removeReference` is a no-op for static values.
