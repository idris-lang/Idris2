# RefC Backend: Cross-Compilation

This document describes how to cross-compile Idris 2 programs to a different
target architecture or operating system using the RefC backend.

## How it works

The RefC backend generates standard C code and then invokes a C compiler (CC)
to produce the final binary.  Cross-compilation is achieved by pointing the
backend at a cross-compiler and/or a sysroot containing the target's headers
and libraries.

Three mechanisms control the cross-compilation flags, in priority order:

| Mechanism | Target triple | Sysroot |
|-----------|--------------|---------|
| `--directive` flag | `--directive "target=<triple>"` | `--directive "sysroot=<path>"` |
| Environment variable | `IDRIS2_CROSS_TRIPLE=<triple>` | `IDRIS2_SYSROOT=<path>` |

The `target` / `IDRIS2_CROSS_TRIPLE` value is passed to the C compiler as
`--target=<triple>` (clang) or it can be used together with a cross-compiler
binary set via `IDRIS2_CC` (GCC).

The `sysroot` / `IDRIS2_SYSROOT` value is passed as `--sysroot=<path>` to
both the compile and link invocations.

Both flags are applied to every CC invocation: object-file compilation,
final link, and incremental-compilation links.

## Example: AArch64 Linux using Clang

Clang supports cross-compilation natively via `--target`:

```sh
IDRIS2_CROSS_TRIPLE=aarch64-linux-gnu \
IDRIS2_SYSROOT=/path/to/aarch64-sysroot \
idris2 --cg refc -o my_app Main.idr
```

Or via directives (useful in project scripts that don't want env vars):

```sh
idris2 --cg refc \
    --directive "target=aarch64-linux-gnu" \
    --directive "sysroot=/path/to/aarch64-sysroot" \
    -o my_app Main.idr
```

## Example: AArch64 Linux using a GCC cross-compiler

GCC cross-compilers encode the target in the binary name, so you only need
to point `IDRIS2_CC` at the right wrapper:

```sh
IDRIS2_CC=aarch64-linux-gnu-gcc \
IDRIS2_SYSROOT=/path/to/aarch64-sysroot \
idris2 --cg refc -o my_app Main.idr
```

## Combining with other flags

All existing environment variables (`IDRIS2_CFLAGS`, `IDRIS2_LDFLAGS`, etc.)
work alongside the cross-compilation flags.  For example, to add optimisation
and pass a custom linker flag:

```sh
IDRIS2_CROSS_TRIPLE=aarch64-linux-gnu \
IDRIS2_CFLAGS="-O2" \
IDRIS2_LDFLAGS="-static" \
idris2 --cg refc -o my_app Main.idr
```

## Directive vs env var precedence

If a `--directive` value is present, it takes priority over the corresponding
environment variable.  This lets a project's build script fix a target while
still allowing the environment to override the sysroot (or vice versa).

## Notes

- `--target` is a clang-style flag.  GCC cross-compilers typically don't
  accept `--target`; use `IDRIS2_CC=<triple>-gcc` instead.
- The runtime libraries (`libidris2_refc`, `libidris2_support`) must be
  compiled for the target.  See `support/refc/` and the Makefile for how to
  build them.
- For bare-metal / freestanding targets see `docs/refc-embedded.md` (Task 12).
