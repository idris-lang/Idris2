#!/bin/sh

set -e # exit on any error

if [ "$(uname)" = Darwin ]; then
    DIR=$(zsh -c 'printf %s "$0:A:h"' "$0")
else
    DIR=$(dirname "$(readlink -f -- "$0")")
fi

LD_LIBRARY_PATH="$DIR/idris2_app":$LD_LIBRARY_PATH
PATH="$DIR/idris2_app":$PATH
export LD_LIBRARY_PATH PATH

"$DIR/idris2_app/idris2-boot" "$@"
