#!/bin/sh

set -e # Exit on any error

echo "bootstrapping IDRIS2_VERSION=$IDRIS2_VERSION"
if [ -z "$IDRIS2_VERSION" ]; then
    echo "Required ENV not set."
    exit 1
fi

# Compile the bootstrap scheme
cd bootstrap
echo "Building idris2-boot from idris2-boot.rkt"
raco exe idris2_app/idris2-boot.rkt

# Put the result in the usual place where the target goes
mkdir -p ../build/exec
mkdir -p ../build/exec/idris2_app
install idris2-rktboot ../build/exec/idris2
install idris2_app/* ../build/exec/idris2_app
