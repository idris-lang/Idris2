#!/bin/sh

set -e # Exit on any error

echo "bootstrapping SCHEME=$SCHEME IDRIS2_VERSION=$IDRIS2_VERSION"
if [ -z "$SCHEME" ] || [ -z "$IDRIS2_VERSION" ]; then
    echo "Required ENV not set."
    if [ -z "$SCHEME" ]; then
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
