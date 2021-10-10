#!/bin/sh

set -e # exit on any error

BOOTEXEC=bootstrap-build/idris2
MAKE=${MAKE:-$(command -v gmake make | head -n 1)}

# Install libraries and support for Stage 1 compiler
"$MAKE" install-support PREFIX="$PWD/bootstrap-build"
for name in prelude base contrib network test; do
    ./$BOOTEXEC --build-dir bootstrap-build --install libs/$name/$name.ipkg
done

# Check it runs / provide debug diagnostics
./$BOOTEXEC -p network --paths

# Stage 2 proper - rebuild everything
"$MAKE" idris2-exec IDRIS2_BOOT=./$BOOTEXEC
"$MAKE" libs
