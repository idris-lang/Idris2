#!/bin/sh

set -e # exit on any error

if [ -z "$SCHEME" ]; then
    echo "Required SCHEME env is not set."
    echo "Invoke with SCHEME=[name of chez scheme executable]"
    exit 1
fi
echo "Bootstrapping SCHEME=$SCHEME"

# Compile the bootstrap scheme
# TODO: Move boot-build to Makefile in bootstrap/Makefile
cd bootstrap-build
echo "Building idris2-boot.so from idris2-boot.ss"
"${SCHEME}" --script ../bootstrap/compile.ss

# Install the launcher script
install ../bootstrap/idris2-boot.sh idris2
