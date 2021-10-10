#!/bin/sh

set -e # exit on any error

if [ -z "$IDRIS2_VERSION" ]; then
    echo "Required IDRIS2_VERSION env is not set."
    exit 1
fi
echo "Bootstrapping IDRIS2_VERSION=$IDRIS2_VERSION"

# Compile the bootstrap scheme
cd bootstrap-build
echo "Building compiled/idris2-boot_rkt.zo from idris2-boot.rkt"
"${RACKET_RACO:-raco}" make idris2_app/idris2-boot.rkt

# Install the launcher script
install ../bootstrap/idris2-rktboot.sh idris2
