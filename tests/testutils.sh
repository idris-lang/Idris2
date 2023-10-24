#!/bin/sh

# This script is intended to be sourced from test scripts.
# It provides a number of test utilities.
# Usage: . ../../testutils.sh

idris2="$1"

# Delete build files between runs to prevent unexpected differences.
# As this is at the top-level, this is run when this script is imported.
rm -rf build
rm -rf prefix

idris2() {
    $idris2 --no-banner --console-width 0 --no-color "$@"
}

check() {
    idris2 --check "$@"
}

run() {
    idris2 --exec main "$@"
}

# Escape a string as a sed pattern literal
# Usage: sed -e "s/$(sed_literal 'some\literal/')/some replacement/g"
sed_literal() {
    # Using printf instead of echo, as echo interprets backslashes as escape sequences on some platforms
    printf '%s\n' "$1" | sed -e 's/[]\/$*.^[]/\\&/g'
}

# Folder containing the currently running test
if [ "$OS" = "windows" ]; then
    test_dir="$(cygpath -m "$(pwd)")"
    SEP=";"
else
    test_dir="$(pwd)"
    SEP=":"
fi

# Set variables for hygiene testing
if [ -z "$PREFIX_CHANGED" ] && [ -n "$IDRIS2_PREFIX" ]; then
    OLD_PREFIX="$IDRIS2_PREFIX"
    NEW_PREFIX="$test_dir/prefix"

    OLD_PP="$OLD_PREFIX/$NAME_VERSION"
    NEW_PP="$NEW_PREFIX/$NAME_VERSION"

    # Set where to look to installed stuff
    export IDRIS2_PACKAGE_PATH="$OLD_PP$SEP$NEW_PP"
    export IDRIS2_LIBS="$OLD_PP/libs$SEP$NEW_PP/libs"
    export IDRIS2_DATA="$OLD_PP/support$SEP$NEW_PP/support"

    # Set where to install stuff
    export IDRIS2_PREFIX="$NEW_PREFIX"

    # Save from re-sourcing this file several times
    export PREFIX_CHANGED=1
fi

# Remove test directory from output
# Useful for consistency of output between machines
# Usage: run SomeTest.idr | filter_test_dir
filter_test_dir() {
    sed -e 's/\\\{1,2\}\b/\//g' | # Guess at where Windows \ need to be replaced by /
        sed -e "s/$(sed_literal "$test_dir")/__TEST_DIR__/g"
}
