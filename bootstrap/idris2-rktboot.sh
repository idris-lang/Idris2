#!/bin/sh

set -e # exit on any error

if [ "$OS" = windows ] || [ "$OS" = Windows_NT ]; then
    DIR=$(dirname "$(readlink -f -- "$0" || cygpath -a -- "$0")")
    PATH=$DIR/idris2_app:$PATH
elif [ "$(uname)" = Darwin ]; then
    DIR=$(zsh -c 'printf %s "$0:A:h"' "$0")
else
    DIR=$(dirname "$(readlink -f -- "$0")")
fi

export LD_LIBRARY_PATH="$DIR/idris2_app:$LD_LIBRARY_PATH"
export DYLD_LIBRARY_PATH="$DIR/idris2_app:$DYLD_LIBRARY_PATH"

${RACKET:=racket} "$DIR/idris2_app/compiled/idris2-boot_rkt.zo" "$@"
