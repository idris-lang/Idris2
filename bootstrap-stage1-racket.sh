#!/bin/sh

set -e # exit on any error

if [ -z "$IDRIS2_VERSION" ]; then
    echo "Required IDRIS2_VERSION env is not set."
    exit 1
fi
echo "Bootstrapping IDRIS2_VERSION=$IDRIS2_VERSION"

# Compile the bootstrap scheme
cd bootstrap
echo "Building idris2-boot from idris2-boot.rkt"
raco exe idris2_app/idris2-boot.rkt

# Put the result in the usual place where the target goes
mkdir -p ../build/exec
mkdir -p ../build/exec/idris2_app
install idris2-rktboot.sh ../build/exec/idris2
install idris2_app/* ../build/exec/idris2_app
