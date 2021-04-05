#!/bin/sh

set -e # exit on any error

if [ -z "$IDRIS2_VERSION" ]; then
    echo "Required IDRIS2_VERSION env is not set."
    exit 1
fi
echo "Bootstrapping IDRIS2_VERSION=$IDRIS2_VERSION"

case $(uname -s) in
    OpenBSD | FreeBSD | NetBSD)
        REALPATH="grealpath"
        ;;

    *)
        REALPATH="realpath"
        ;;
esac

if ! command -v "$REALPATH" >/dev/null; then
    echo "$REALPATH is required for Racket code generator."
    exit 1
fi

DIR=$(dirname "$($REALPATH "$0")")
LD_LIBRARY_PATH="$DIR/idris2_app":$LD_LIBRARY_PATH
PATH="$DIR/idris2_app":$PATH
export LD_LIBRARY_PATH PATH

"$DIR/idris2_app/idris2-boot" "$@"
