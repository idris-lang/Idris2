#!/bin/sh

set -e  # Exit on any error

echo "bootstrapping SCHEME=$SCHEME IDRIS2_VERSION=$IDRIS2_VERSION"
if [ -z "$SCHEME" ] || [ -z "$IDRIS2_VERSION" ]
then
    echo "Required ENV not set."
    if [ -z "$SCHEME" ]
    then
        echo "Invoke with SCHEME=[name of chez scheme executable]"
    fi
    exit 1
fi

# Compile the bootstrap scheme
# TODO: Move boot-build to Makefile in bootstrap/Makefile
cd bootstrap
echo "Building idris2-boot from idris2-boot.ss"
${SCHEME} --script compile.ss

# Put the result in the usual place where the target goes
mkdir -p ../build/exec
mkdir -p ../build/exec/idris2_app
install idris2-boot ../build/exec/idris2
install idris2_app/* ../build/exec/idris2_app

cd ..

# TODO: Unify with bootstrap-rkt
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
${MAKE} libs SCHEME=${SCHEME} PREFIX=${PREFIX}
${MAKE} install SCHEME=${SCHEME} PREFIX=${PREFIX}
${MAKE} clean IDRIS2_BOOT=${PREFIX}/bin/idris2
${MAKE} all IDRIS2_BOOT=${PREFIX}/bin/idris2 SCHEME=${SCHEME} IDRIS2_PATH=${IDRIS2_BOOT_PATH}
