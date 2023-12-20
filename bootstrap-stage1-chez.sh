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
echo "Building idris2-boot from idris2-boot.ss"
${SCHEME} --script ../bootstrap/compile.ss

# Put the result in the usual place where the target goes
mkdir -p ../build/exec
mkdir -p ../build/exec/idris2_app

# we "install" bootstrap/idris2-boot.sh as build/exec/idris2
# but with the SCHEME var that we already know at this time
# baked into it.
echo '#!/bin/sh' >../build/exec/idris2
echo "SCHEME=${SCHEME}" >>../build/exec/idris2
cat ../bootstrap/idris2-boot.sh >>../build/exec/idris2
chmod +x ../build/exec/idris2

install idris2_app/* ../build/exec/idris2_app
echo 'bootstrap stage 1 complete'
