#!/bin/sh

# This script is intended to be sourced from test scripts.
# It provides a number of test utilities.
# Usage: . ../../testutils.sh

idris2="$1"

# Delete build files between runs to prevent unexpected differences.
# As this is at the top-level, this is run when this script is imported.
rm -rf build

idris2() {
    $idris2 --no-banner --console-width 0 --no-color "$@"
}

check() {
    idris2 --check "$@"
}

run() {
    idris2 --exec main "$@"
}
