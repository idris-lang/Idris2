#!/bin/sh

# Compile the bootstrap scheme
cd bootstrap
echo "Building idris2boot from idris2boot.rkt"

raco exe idris2boot.rkt

# Put the result in the usual place where the target goes
mkdir -p ../build/exec
install idris2boot ../build/exec/idris2

cd ..

# Install with the bootstrap directory as the PREFIX
DIR="`realpath $0`"
PREFIX="`dirname $DIR`"/bootstrap

# Now rebuild everything properly
echo ${PREFIX}
IDRIS2_BOOT_PATH="${PREFIX}/idris2-0.2.0/prelude:${PREFIX}/idris2-0.2.0/base:${PREFIX}/idris2-0.2.0/contrib:${PREFIX}/idris2-0.2.0/network"
DYLIB_PATH="${PREFIX}/lib"

make libs CG=racket PREFIX=${PREFIX} LD_LIBRARY_PATH=${DYLIB_PATH}
make install CG=racket PREFIX=${PREFIX} LD_LIBRARY_PATH=${DYLIB_PATH}
make clean IDRIS2_BOOT=${PREFIX}/bin/idris2 LD_LIBRARY_PATH=${DYLIB_PATH}
make all IDRIS2_BOOT=${PREFIX}/bin/idris2 CG=racket IDRIS2_PATH=${IDRIS2_BOOT_PATH} LD_LIBRARY_PATH=${DYLIB_PATH}
#make test INTERACTIVE='' IDRIS2_BOOT=${PREFIX}/bin/idris2 CG=racket IDRIS2_PATH=${IDRIS2_BOOT_PATH} IDRIS2_LIBS=${PREFIX}/idris2-0.2.0/lib LD_LIBRARY_PATH=${DYLIB_PATH}
