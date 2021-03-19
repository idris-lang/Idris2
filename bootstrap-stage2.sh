#!/bin/sh

set -e # exit on any error

PREFIX=$PWD/bootstrap

if [ "$OS" = "windows" ]; then
    # IDRIS_PREFIX is only used to build IDRIS2_BOOT_PATH
    IDRIS_PREFIX=$(cygpath -m "$PREFIX")
    SEP=";"
else
    IDRIS_PREFIX=$PREFIX
    SEP=":"
fi

IDRIS2_CG="${IDRIS2_CG-"chez"}"

BOOT_PATH_BASE=$IDRIS_PREFIX/idris2-$IDRIS2_VERSION
IDRIS2_BOOT_PATH="$BOOT_PATH_BASE/prelude$SEP	$BOOT_PATH_BASE/base$SEP	$BOOT_PATH_BASE/contrib$SEP	$BOOT_PATH_BASE/network	$BOOT_PATH_BASE/test"

# PREFIX must be the "clean" build root, without cygpath -m
# Otherwise, we get 'git: Bad address'
echo "$PREFIX"
DYLIB_PATH="$PREFIX/lib"

$MAKE libs IDRIS2_CG="$IDRIS2_CG" LD_LIBRARY_PATH="$DYLIB_PATH" \
    PREFIX="$PREFIX" SCHEME="$SCHEME"
$MAKE install IDRIS2_CG="$IDRIS2_CG" LD_LIBRARY_PATH="$DYLIB_PATH" \
    PREFIX="$PREFIX" SCHEME="$SCHEME"

# Now rebuild everything properly
$MAKE clean-libs IDRIS2_BOOT="$PREFIX/bin/idris2"
$MAKE all IDRIS2_BOOT="$PREFIX/bin/idris2" IDRIS2_CG="$IDRIS2_CG" \
    IDRIS2_PATH="$IDRIS2_BOOT_PATH" LD_LIBRARY_PATH="$DYLIB_PATH" \
    SCHEME="$SCHEME"
