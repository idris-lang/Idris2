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
cd bootstrap-build
echo "Building idris2-boot.so from idris2-boot.ss"
"${SCHEME}" --script ../bootstrap/compile.ss

# Install the launcher script
install ../bootstrap/idris2-boot.sh idris2
