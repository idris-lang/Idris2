#!/bin/sh

set -e # exit on any error

if [ -z "$SCHEME" ]; then
    echo "Required SCHEME env is not set."
    exit 1
fi

case $(uname -s) in
    OpenBSD | FreeBSD | NetBSD)
        REALPATH="grealpath"
        ;;

    *)
        REALPATH="realpath"
        ;;
esac

if ! command -v "$REALPATH" >/dev/null; then
    echo "$REALPATH is required for Chez code generator."
    exit 1
fi

DIR=$(dirname "$($REALPATH "$0")")
LD_LIBRARY_PATH="$DIR/idris2_app":$LD_LIBRARY_PATH
PATH="$DIR/idris2_app":$PATH
export LD_LIBRARY_PATH PATH

${SCHEME} --script "$DIR/idris2_app/idris2-boot.so" "$@"
