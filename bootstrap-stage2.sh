#!/bin/sh

set -e # exit on any error

IDRIS2_CG="${IDRIS2_CG-"chez"}"

# IDRIS2_BOOT_PREFIX must be the "clean" build root, without cygpath -m
# Otherwise, we get 'git: Bad address'
echo "[bootstrap] bootstrapping in: $IDRIS2_BOOT_PREFIX"
export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-"${IDRIS2_BOOT_PREFIX}/idris2-0.7.0/lib"}"
export DYLD_LIBRARY_PATH="${DYLD_LIBRARY_PATH:-"${IDRIS2_BOOT_PREFIX}/idris2-0.7.0/lib"}"
export PATH="${PATH:-"${IDRIS2_BOOT_PREFIX}/idris2-0.7.0/lib"}"
export IDRIS2_DATA="${IDRIS2_DATA:-"${IDRIS2_BOOT_PREFIX}/idris2-0.7.0/support"}"

$MAKE bootstrap-libs IDRIS2_CG="$IDRIS2_CG" \
    PREFIX="$IDRIS2_BOOT_PREFIX" SCHEME="$SCHEME"
$MAKE bootstrap-install IDRIS2_CG="$IDRIS2_CG" \
    PREFIX="$IDRIS2_BOOT_PREFIX" SCHEME="$SCHEME"

# Now rebuild everything properly
echo '[bootstrap] cleaning and rebuilding...'
$MAKE clean-libs IDRIS2_BOOT="$IDRIS2_BOOT_PREFIX/bin/idris2"
echo "triage -- $(ls ${IDRIS2_BOOT_PREFIX})"
echo "triage -- $(ls ${IDRIS2_BOOT_PREFIX}/idris2-*/lib)"
$MAKE all IDRIS2_BOOT="$IDRIS2_BOOT_PREFIX/bin/idris2" IDRIS2_CG="$IDRIS2_CG" \
    SCHEME="$SCHEME"
echo '[bootstrap] stage 2 complete'
