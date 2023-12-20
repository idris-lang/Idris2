#!/bin/sh

set -e # exit on any error

BOOTSTRAP_PREFIX=$PWD/bootstrap-build

IDRIS2_CG="${IDRIS2_CG-"chez"}"

# BOOTSTRAP_PREFIX must be the "clean" build root, without cygpath -m
# Otherwise, we get 'git: Bad address'
echo "bootstrapping in: $BOOTSTRAP_PREFIX"
export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-"${BOOTSTRAP_PREFIX}/lib"}"
export DYLD_LIBRARY_PATH="${DYLD_LIBRARY_PATH:-"${BOOTSTRAP_PREFIX}/lib"}"
export IDRIS2_DATA="${IDRIS2_DATA:-"${BOOTSTRAP_PREFIX}/support"}"

$MAKE bootstrap-libs IDRIS2_CG="$IDRIS2_CG" \
    PREFIX="$BOOTSTRAP_PREFIX" SCHEME="$SCHEME"
$MAKE bootstrap-install IDRIS2_CG="$IDRIS2_CG" \
    PREFIX="$BOOTSTRAP_PREFIX" SCHEME="$SCHEME"

# Now rebuild everything properly
$MAKE clean-libs IDRIS2_BOOT="$BOOTSTRAP_PREFIX/bin/idris2"
$MAKE all IDRIS2_BOOT="$BOOTSTRAP_PREFIX/bin/idris2" IDRIS2_CG="$IDRIS2_CG" \
    SCHEME="$SCHEME"
echo 'bootstrap stage 2 complete'
