#!/bin/sh

set -e # exit on any error

if [ "$OS" = windows ] || [ "$OS" = Windows_NT ]; then
    BOOTSTRAP_PREFIX=$(cygpath -m "$PWD")/bootstrap-build
else
    BOOTSTRAP_PREFIX=$PWD/bootstrap-build
fi

IDRIS2_CG="${IDRIS2_CG-"chez"}"

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
