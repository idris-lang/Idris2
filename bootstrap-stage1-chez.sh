#!/bin/sh

set -e # exit on any error

if [ -z "$SCHEME" ] || [ -z "$IDRIS2_VERSION" ]; then
    echo "Required SCHEME or IDRIS2_VERSION env is not set."
    if [ -z "$SCHEME" ]; then
        echo "Invoke with SCHEME=[name of chez scheme executable]"
    fi
    exit 1
fi
echo "Bootstrapping SCHEME=$SCHEME IDRIS2_VERSION=$IDRIS2_VERSION"

# Compile the bootstrap scheme
# TODO: Move boot-build to Makefile in bootstrap/Makefile
cd bootstrap
echo "Building idris2-boot from idris2-boot.ss"
${SCHEME} --script compile.ss

# Put the result in the usual place where the target goes
mkdir -p ../build/exec
mkdir -p ../build/exec/idris2_app
install idris2-boot.sh ../build/exec/idris2
install idris2_app/* ../build/exec/idris2_app
