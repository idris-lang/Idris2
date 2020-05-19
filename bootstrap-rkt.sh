#!/bin/sh

# Compile the bootstrap scheme
cd bootstrap
echo "Building idris2boot from idris2boot.rkt"

raco exe idris2boot.rkt

# Put the result in the usual place where the target goes
mkdir -p ../build/exec
install idris2boot ../build/exec/idris2sh

cd ..

# Install with the bootstrap directory as the PREFIX
DIR="`realpath $0`"
PREFIX="`dirname $DIR`"/bootstrap

# Now rebuild everything properly
echo ${PREFIX}

IDRIS2_BOOT_PATH="${PREFIX}/idris2-0.2.0/prelude:${PREFIX}/idris2-0.2.0/base:${PREFIX}/idris2-0.2.0/contrib:${PREFIX}/idris2-0.2.0/network"

make libs CG=racket PREFIX=${PREFIX}
make install CG=racket PREFIX=${PREFIX}
make clean
make all IDRIS2_BOOT=${PREFIX}/bin/idris2sh CG=racket IDRIS2_PATH=${IDRIS2_BOOT_PATH}
