# RefC FFI Guide: Writing C Bindings for the RefC Backend

This guide explains how to expose C functions to Idris 2 programs
compiled with the RefC backend (`--cg refc`).

---

## 1. Quick Example

```c
// mylib.c
#include "cBackend.h"   // included automatically; defines Value, etc.

Value *mylib_add(Value *a, Value *b) {
    int64_t x = idris2_vp_to_Int64(a);
    int64_t y = idris2_vp_to_Int64(b);
    idris2_removeReference(a);
    idris2_removeReference(b);
    return (Value *)idris2_mkInt64(x + y);
}
```

```idris
-- Main.idr
%foreign "C:mylib_add, mylib.h"
prim__add : Int -> Int -> Int

main : IO ()
main = printLn $ prim__add 3 4   -- prints 7
```

Build:
```sh
idris2 --cg refc -o prog Main.idr CFLAGS="-I. mylib.c"
```

---

## 2. The `%foreign` Declaration

```idris
%foreign "C:c_function_name[, header.h]"
prim__myFunc : ArgType1 -> ArgType2 -> ReturnType
```

- **`C:`** — standard C calling convention; the generated wrapper
  extracts each Idris argument to the appropriate C type before calling.
- **`RefC:`** — same as `C:` but for functions whose signature already
  accepts/returns `Value *` directly (see §4).
- The optional `header.h` causes `#include "header.h"` to be emitted in
  the generated C file.

For `PrimIO` functions add the world token as the last argument:
```idris
%foreign "C:mylib_io_func, mylib.h"
prim__ioFunc : Int -> PrimIO Int
-- equivalent Idris type: Int -> (1 _ : %World) -> IORes Int
```

---

## 3. Type Mapping

| Idris type      | C type extracted by codegen | Pack function (C → Idris)    |
|-----------------|----------------------------|-------------------------------|
| `Int`           | `int64_t`                  | `idris2_mkInt64`              |
| `Int8`          | `int8_t`                   | `idris2_mkInt8`               |
| `Int16`         | `int16_t`                  | `idris2_mkInt16`              |
| `Int32`         | `int32_t`                  | `idris2_mkInt32`              |
| `Int64`         | `int64_t`                  | `idris2_mkInt64`              |
| `Bits8`         | `uint8_t`                  | `idris2_mkBits8`              |
| `Bits16`        | `uint16_t`                 | `idris2_mkBits16`             |
| `Bits32`        | `uint32_t`                 | `idris2_mkBits32`             |
| `Bits64`        | `uint64_t`                 | `idris2_mkBits64`             |
| `Double`        | `double`                   | `idris2_mkDouble`             |
| `Char`          | `int` (Unicode codepoint)  | `idris2_mkChar`               |
| `String`        | `char *`                   | `idris2_mkString`             |
| `Ptr t`         | `void *`                   | `idris2_mkPtr`                |
| `AnyPtr`        | `void *`                   | `idris2_mkPtr`                |
| `()` / `Unit`   | *(return `NULL`)*          | *(return `NULL`)*             |

The codegen emits extraction calls automatically. For example, a
declaration `%foreign "C:f" prim__f : Int -> Int` generates:

```c
Value *prim__f_wrapper(Value *var_0) {
    int64_t arg0 = idris2_vp_to_Int64(var_0);
    idris2_removeReference(var_0);           // ← emitted by codegen
    int64_t retVal = f(arg0);
    return (Value *)idris2_mkInt64(retVal);
}
```

---

## 4. The `RefC:` Calling Convention

Use `RefC:` when your C function works with `Value *` directly and
handles reference counting itself:

```c
// Works on any Value, not just a specific primitive type
Value *mylib_identity(Value *v) {
    return v;   // no removeReference — ownership is passed through
}
```

```idris
%foreign "RefC:mylib_identity"
prim__id : a -> a
```

With `RefC:`, the codegen does **not** extract arguments or pack the
return value — it passes `Value *` pointers straight through.

---

## 5. Reference Counting Contract

This is the most important rule for FFI functions:

> **The generated wrapper already calls `idris2_removeReference` for
> every argument before returning. FFI functions must NOT call
> `idris2_removeReference` on their own arguments.**

### What this means in practice

For `C:` functions (primitive extraction):

- You receive extracted C values (`int64_t`, `char *`, etc.), not `Value *`.
- You never touch reference counts — the wrapper does it for you.
- Return a freshly allocated `Value *` (refcount = 1) or an unboxed value.

For `RefC:` functions (raw `Value *`):

- The wrapper **does NOT call removeReference** on args — you own each arg.
- You must call `idris2_removeReference(arg)` for every arg you do not
  store or return. Failing to do so leaks memory.
- Return a `Value *` with refcount = 1 (or an unboxed value, or NULL for Unit).

### Sharing a value

If you want to *keep* a `Value *` and also *return* it (or store it),
call `idris2_newReference` first to increment the refcount:

```c
Value *mylib_store_and_return(Value *v) {
    global_cache = idris2_newReference(v);  // now two owners
    return v;                                // caller owns the original ref
}
```

### The zero refcount (static values)

Values with `header.refCounter == 0` are static (compile-time constants).
`idris2_removeReference` and `idris2_newReference` are both no-ops for
them. You never need to special-case this — the runtime handles it.

---

## 6. Strings

Strings are heap-allocated `Value_String` with an inline char array.

**Extracting a string argument:**
```c
Value *mylib_print(Value *s) {
    // s is already extracted to char* by the C: wrapper; but if using RefC:
    char *str = ((Value_String *)s)->str;
    printf("%s\n", str);
    idris2_removeReference(s);
    return NULL;
}
```

**Returning a new string:**
```c
Value *mylib_greeting(void) {
    return (Value *)idris2_mkString("hello");  // allocates + copies
}
```

`idris2_mkString` allocates a new `Value_String` and copies the chars.
The caller owns the returned pointer (refcount = 1).

---

## 7. Pointers

Wrap a raw C pointer with `idris2_mkPtr` / `idris2_mkAnyPtr`:
```c
Value *mylib_open(void) {
    FILE *f = fopen("x.txt", "r");
    return (Value *)idris2_mkPtr(f);
}
```

Extract with `idris2_vp_to_Ptr`:
```c
Value *mylib_close(Value *p) {
    FILE *f = (FILE *)idris2_vp_to_Ptr(p);
    fclose(f);
    idris2_removeReference(p);
    return NULL;
}
```

For a GC-managed pointer with a finaliser, use `onCollect`/`onCollectAny`
from `Prelude.IO` rather than `Ptr`.

---

## 8. Unimplemented FFI

If a `%foreign` declaration has no `C:` or `RefC:` binding (e.g., only
a `scheme:` binding), the RefC codegen emits a *named stub*:

```c
static void Main_prim__schemeOnlyFunc_refc_unimplemented() {
    fprintf(stderr,
        "ERROR: FFI function not implemented for the RefC backend:\n"
        "  Main.prim__schemeOnlyFunc\n"
        "(Add a \"C:\" or \"RefC:\" %%foreign binding.)\n");
    exit(1);
}
```

The program compiles successfully; the error only fires if the stub is
actually called at runtime. This lets programs that are mostly portable
compile and run even if a few scheme-only functions are never reachable.

---

## 9. Debug Build

To compile with debug symbols and `#line` directives that map generated
C back to Idris source:

```sh
idris2 --cg refc --directive debug -o prog Main.idr
```

The `--directive debug` flag passes `-g` to the C compiler. The generated
`.c` file also contains `#line N "Module.Name"` directives so that
`gdb`/`lldb` stack traces show Idris source locations.
