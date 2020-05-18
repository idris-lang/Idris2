#!/bin/sh

cd bootstrap
${SCHEME} --script compile.ss

mkdir -p ../build/exec
mkdir -p ../build/exec/idris2sh_app
install idris2-boot ../build/exec/idris2sh
install idris2sh_app/* ../build/exec/idris2sh_app
