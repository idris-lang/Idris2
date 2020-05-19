#!/bin/sh

if [ -z "$SCHEME" ]
then
    echo "SCHEME not set. Invoke with SCHEME=[name of chez executable]"
    exit 1
fi

# Compile the bootstrap scheme
cd bootstrap
${SCHEME} --script compile.ss

# Put the result in the usual place where the target goes
mkdir -p ../build/exec
mkdir -p ../build/exec/idris2sh_app
install idris2-boot ../build/exec/idris2sh
install idris2sh_app/* ../build/exec/idris2sh_app

# Install with the bootstrap directory as the PREFIX
DIR="`realpath $0`"
PREFIX="`dirname $0`"/bootstrap

cd ..

# Now rebuuld everything properly
make libs SCHEME=${SCHEME} PREFIX=${PREFIX}
make install SCHEME=${SCHEME} PREFIX=${PREFIX}
make clean
make all IDRIS2_BOOT=${PREFIX}/bin/idris2sh SCHEME=${SCHEME}
