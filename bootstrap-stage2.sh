#!/bin/sh

set -e # exit on any error

BOOTSTRAP_PREFIX=$PWD/bootstrap-build

if [ "$OS" = "windows" ]; then
    # IDRIS_PREFIX is only used to build IDRIS2_BOOT_PATH
    IDRIS_PREFIX=$(cygpath -m "$BOOTSTRAP_PREFIX")
    SEP=";"
else
    IDRIS_PREFIX=$BOOTSTRAP_PREFIX
    SEP=":"
fi

IDRIS2_CG="${IDRIS2_CG-"chez"}"

BOOT_PATH_BASE=$IDRIS_PREFIX/idris2-$IDRIS2_VERSION
IDRIS2_BOOT_PATH="$BOOT_PATH_BASE/prelude$SEP	$BOOT_PATH_BASE/base$SEP	$BOOT_PATH_BASE/contrib$SEP	$BOOT_PATH_BASE/network	$BOOT_PATH_BASE/test"

# BOOTSTRAP_PREFIX must be the "clean" build root, without cygpath -m
# Otherwise, we get 'git: Bad address'
echo "$BOOTSTRAP_PREFIX"
DYLIB_PATH="$BOOTSTRAP_PREFIX/lib"

$MAKE install-support PREFIX="$BOOTSTRAP_PREFIX"
$MAKE install-libs PREFIX="$BOOTSTRAP_PREFIX" TARGET=$BOOTSTRAP_PREFIX/idris2 \
    IDRIS2_BOOT_PATH="$IDRIS2_BOOT_PATH"

# Now rebuild everything properly
$MAKE clean-libs IDRIS2_BOOT="$BOOTSTRAP_PREFIX/bin/idris2"
$MAKE all IDRIS2_BOOT="$BOOTSTRAP_PREFIX/bin/idris2" IDRIS2_CG="$IDRIS2_CG" \
    IDRIS2_PATH="$IDRIS2_BOOT_PATH" LD_LIBRARY_PATH="$DYLIB_PATH" \
    SCHEME="$SCHEME"
