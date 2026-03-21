# RefC Reference Counting Contract

A precise specification of ownership and reference counting rules for code
that works directly with `Value *` — including FFI authors, runtime
contributors, and anyone reading generated C.

---

## 1. Core Invariant

> **Every live `Value *` is owned by exactly one slot (variable, field,
> or return value). The owner is responsible for eventually calling
> `idris2_removeReference` — or transferring ownership to a new owner.**

"Live" means the value will be read again. Once you are done with a value
and will not read it or pass it on, call `idris2_removeReference` to
release your ownership.

---

## 2. Reference Count Semantics

| `refCounter` value | Meaning |
|--------------------|---------|
| `0`                | Static value (compile-time constant). Never freed. `newReference` and `removeReference` are no-ops. |
| `1`                | Unique — owned by exactly one slot. Can be mutated or freed directly. |
| `> 1`              | Shared — owned by multiple slots. Must copy-on-write before mutating; `removeReference` only decrements. |

The runtime exposes:

```c
Value *idris2_newReference(Value *v);   // v->refCounter++; return v
void   idris2_removeReference(Value *v); // if --v->refCounter == 0: free recursively
bool   idris2_isUnique(Value *v);        // refCounter == 1
```

`idris2_newReference` returns its argument so it can be used inline.

---

## 3. Ownership Transfer Rules

### 3.1 Function call — arguments

When you pass a `Value *` to any function (generated or runtime), you
**transfer ownership** of that pointer to the callee. You must not read or
free the pointer after the call unless you first increment the refcount:

```c
// WRONG — use-after-transfer:
Value *v = idris2_mkInt64(42);
some_function(v);
idris2_removeReference(v);   // double-free if some_function freed it

// CORRECT — keep a reference if you need to continue using it:
Value *v = idris2_mkInt64(42);
some_function(idris2_newReference(v));   // callee owns the extra ref
idris2_removeReference(v);              // we release our copy when done
```

### 3.2 Function return — return values

A function that returns a `Value *` transfers ownership to the caller.
The caller must eventually call `idris2_removeReference` on it (or pass
it on).

```c
Value *result = some_function(...);
// use result ...
idris2_removeReference(result);   // caller releases when done
```

Allocation functions (`idris2_mkInt64`, `idris2_mkString`, …) return a
freshly allocated value with `refCounter = 1`. You own it.

### 3.3 Storing a value

If you store a `Value *` in a data structure (e.g. a constructor field,
a global cache), you must call `idris2_newReference` to record the
additional owner:

```c
Value *global_cache;

void cache_value(Value *v) {
    // we receive ownership of v, then want to store it AND return it
    global_cache = idris2_newReference(v);   // cache is now a second owner
    // we still own the original ref — caller gets it back via return
}
```

When removing a value from a data structure, call `idris2_removeReference`
to release the structure's ownership:

```c
void clear_cache(void) {
    if (global_cache) {
        idris2_removeReference(global_cache);
        global_cache = NULL;
    }
}
```

---

## 4. FFI-Specific Rules

### 4.1 `C:` convention (primitive extraction)

The generated wrapper extracts each argument to a C primitive
(`int64_t`, `char *`, etc.) and calls `idris2_removeReference` on the
`Value *` **before** calling your function. Your function:

- Receives plain C values, not `Value *`.
- Must NOT touch reference counts.
- Must return either an unboxed value or a freshly allocated `Value *`
  (refcount = 1).

```c
// Correct C: function
int64_t mylib_add(int64_t a, int64_t b) {
    return a + b;   // codegen wraps the result in idris2_mkInt64
}
```

### 4.2 `RefC:` convention (raw `Value *`)

The generated wrapper passes `Value *` pointers straight through —
**no extraction, no automatic removeReference**. Your function owns
every argument and must handle its lifetime:

```c
// Correct RefC: function — consumes both args
Value *mylib_add(Value *a, Value *b) {
    int64_t x = idris2_vp_to_Int64(a);
    int64_t y = idris2_vp_to_Int64(b);
    idris2_removeReference(a);    // release ownership — we won't use a again
    idris2_removeReference(b);    // same for b
    return (Value *)idris2_mkInt64(x + y);   // caller owns the result
}
```

If you want to return one of the arguments unchanged (identity-like):

```c
// Pass-through — ownership flows to the caller
Value *mylib_identity(Value *v) {
    return v;   // do NOT removeReference — ownership transferred to caller
}
```

If you want to store an arg AND return it, increment the refcount first:

```c
Value *mylib_store_and_return(Value *v) {
    global_cache = idris2_newReference(v);  // cache holds one ref
    return v;                               // caller gets the original ref
}
```

### 4.3 Summary table

| Situation | Action |
|-----------|--------|
| Arg you will read and then discard | `idris2_removeReference(arg)` after last use |
| Arg you will return (pass through) | Return it directly — no refcount change |
| Arg you will store AND return | `idris2_newReference(arg)` before storing; return arg |
| Arg you will store but NOT return | Store directly (you own it); do not removeReference yet |
| Freshly allocated value you return | Return directly (refcount = 1 is correct) |
| Freshly allocated value you discard | `idris2_removeReference(it)` |

---

## 5. The `idris2_isUnique` Fast Path

When `refCounter == 1` the value has a single owner — it can be mutated
in place or its allocation reused. The runtime uses this in several places:

- **Closure application**: if the closure is unique, captured args are
  moved (no `newReference`), avoiding N increments.
- **Constructor reuse** (`IDRIS2_REUSE`): the codegen may reuse a
  scrutinised constructor's memory for the result when it is unique.

FFI authors rarely need `idris2_isUnique` directly, but it is available
for write-optimised data structures that want copy-on-write semantics:

```c
Value_Constructor *idris2_unique_or_copy(Value_Constructor *c) {
    if (idris2_isUnique((Value *)c)) return c;   // mutate in place
    // make a fresh copy, decrement c's refcount
    Value_Constructor *copy = /* allocate and copy fields */;
    idris2_removeReference((Value *)c);
    return copy;
}
```

---

## 6. Static Values

Values with `refCounter == 0` are compile-time constants. Both
`idris2_newReference` and `idris2_removeReference` check for this and
are no-ops. You never need to special-case static values in FFI code —
the runtime handles it transparently.

Common static values:

- Predefined small integers (`idris2_predefined_Int64`)
- Compile-time string literals (`IDRIS2_STOCKVAL`)
- Predefined constructors: `True`, `False`, `Nothing`, `()`, `Nil`

---

## 7. Common Mistakes

### Double-free

```c
// WRONG
idris2_removeReference(v);
idris2_removeReference(v);   // UB — v may already be freed
```

### Use-after-free

```c
// WRONG
idris2_removeReference(v);
int64_t x = idris2_vp_to_Int64(v);   // v may be freed
```

### Leak (forgot to release)

```c
// WRONG — v is never freed
Value *v = idris2_mkInt64(42);
// ... v never passed anywhere, never removeReference'd
```

### Returning an arg without adjusting refcount when also storing it

```c
// WRONG — two owners, only one ref
Value *bad(Value *v) {
    global_cache = v;   // stored
    return v;           // also returned — now two owners share one refcount
    // correct: global_cache = idris2_newReference(v); return v;
}
```

---

## 8. Quick Reference

```c
// Allocate (refcount = 1, you own it)
Value *v = (Value *)idris2_mkInt64(x);
Value *s = (Value *)idris2_mkString("hello");

// Add an owner
idris2_newReference(v);     // refcount++

// Release ownership (frees if last owner)
idris2_removeReference(v);  // refcount--; free if 0

// Check uniqueness (single owner)
if (idris2_isUnique(v)) { /* safe to mutate in place */ }

// Extract primitives from Value*
int64_t  n = idris2_vp_to_Int64(v);
uint32_t u = idris2_vp_to_Bits32(v);
double   d = idris2_vp_to_Double(v);
char    *s = ((Value_String *)v)->str;
void    *p = idris2_vp_to_Ptr(v);
```
