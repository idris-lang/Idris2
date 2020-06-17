#!/bin/sh

set -e  # Exit on any error

echo "bootstrapping IDRIS2_VERSION=$IDRIS2_VERSION"
if [ -z "$IDRIS2_VERSION" ]
then
    echo "Required ENV not set."
    exit 1
fi

# Compile the bootstrap scheme
cd bootstrap
echo "Building idris2-boot from idris2-boot.rkt"
raco exe idris2_app/idris2-boot.rkt

# Put the result in the usual place where the target goes
mkdir -p ../build/exec
mkdir -p ../build/exec/idris2_app
install idris2-rktboot ../build/exec/idris2
install idris2_app/* ../build/exec/idris2_app

cd ..

PREFIX=${PWD}/bootstrap

if [ ${OS} = "windows" ]; then
    # IDRIS_PREFIX is only used to build IDRIS2_BOOT_PATH
    IDRIS_PREFIX=$(cygpath -m $PREFIX)
    SEP=";"
else
    IDRIS_PREFIX=${PREFIX}
    SEP=":"
fi

BOOT_PATH_BASE=${IDRIS_PREFIX}/idris2-${IDRIS2_VERSION}
IDRIS2_BOOT_PATH="${BOOT_PATH_BASE}/prelude${SEP}${BOOT_PATH_BASE}/base${SEP}${BOOT_PATH_BASE}/contrib${SEP}${BOOT_PATH_BASE}/network"

# Now rebuild everything properly
# PREFIX must be the "clean" build root, without cygpath -m
# Otherwise, we get 'git: Bad address'
echo ${PREFIX}
DYLIB_PATH="${PREFIX}/lib"
${MAKE} libs IDRIS2_CG=racket PREFIX=${PREFIX} LD_LIBRARY_PATH=${DYLIB_PATH}
${MAKE} install IDRIS2_CG=racket PREFIX=${PREFIX} LD_LIBRARY_PATH=${DYLIB_PATH}
${MAKE} clean IDRIS2_BOOT=${PREFIX}/bin/idris2 LD_LIBRARY_PATH=${DYLIB_PATH}
${MAKE} all IDRIS2_BOOT=${PREFIX}/bin/idris2 IDRIS2_CG=racket IDRIS2_PATH=${IDRIS2_BOOT_PATH} LD_LIBRARY_PATH=${DYLIB_PATH}
