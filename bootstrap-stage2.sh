#!/bin/sh

set -e # exit on any error

BOOTSTRAP_PREFIX=$PWD/bootstrap-build
IDRIS2_CG="${IDRIS2_CG-"chez"}"

# BOOTSTRAP_PREFIX must be the "clean" build root, without cygpath -m
# Otherwise, we get 'git: Bad address'
echo "$BOOTSTRAP_PREFIX"

$MAKE libs IDRIS2_CG="$IDRIS2_CG" \
    PREFIX="$BOOTSTRAP_PREFIX" SCHEME="$SCHEME"
$MAKE install IDRIS2_CG="$IDRIS2_CG" \
    PREFIX="$BOOTSTRAP_PREFIX" SCHEME="$SCHEME"

# Now rebuild everything properly
$MAKE clean-libs IDRIS2_BOOT="$BOOTSTRAP_PREFIX/bin/idris2"
$MAKE all IDRIS2_BOOT="$BOOTSTRAP_PREFIX/bin/idris2" IDRIS2_CG="$IDRIS2_CG" \
    SCHEME="$SCHEME"
