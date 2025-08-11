#!/bin/sh

# This script is intended to be sourced from test scripts.
# It provides a number of test utilities.
# Usage: . ../../testutils.sh

idris2="$1"

# Delete build files between runs to prevent unexpected differences.
# As this is at the top-level, this is run when this script is imported.
rm -rf build
rm -rf prefix

if type valgrind >/dev/null 2>&1; then
    export VALGRIND="valgrind --leak-check=full -s --log-file=output.valgrind.refc.log"
else
    unset VALGRIND
fi

idris2() {
    $idris2 --no-banner --console-width 0 --no-color "$@"
}

check() {
    idris2 --check "$@"
}

run() {
    idris2 --exec main "$@"
}

safesort() {
    LC_ALL=C.UTF-8 sort
}

# Escape a string as a sed pattern literal
# Usage: sed -e "s/$(sed_literal 'some\literal/')/some replacement/g"
sed_literal() {
    # Using printf instead of echo, as echo interprets backslashes as escape sequences on some platforms
    printf '%s\n' "$1" | sed -e 's/[]\/$*.^[]/\\&/g'
}

windows_path_tweaks() {
    sed 's#C:.msys64##' | sed 's#\\#/#g'
}

# used below to normalise machine names
# shellcheck disable=SC2016
_awk_clean_name='
#!/bin/awk -f
# consistently replace numbers to make golden tests more stable. Currently handles:
#   {xyz:NNN
#   $resolvedNNN
#   ttc/NNNNNNNNNN
#   Foo.Bar:NN:NN--NN:NN
#   P:xyz:NNNNN
{
    idPat = "[_a-zA-Z][_a-zA-Z0-9]*"
    numPat = "[0-9]+"
    namePat = idPat "([.]" idPat ")*"

    mainPat = "P:" idPat ":" numPat \
          "|" "[{]" idPat ":" numPat \
          "|" "ttc[\\\\/]" numPat \
          "|" "[$]resolved" numPat \
          "|" namePat ":" numPat ":" numPat "--" numPat ":" numPat \
          "|" namePat "[.]" numPat ":" numPat

    prefixPat = "P:" idPat ":" \
            "|" "[{]" idPat ":" \
            "|" "ttc[\\\\/]" \
            "|" "[$]resolved" \
            "|" namePat ":" \
            "|" namePat "[.]"

    out = ""
    # the last one is FC
    while (match($0, mainPat)) {
        rs = RSTART
        rl = RLENGTH
        m = substr($0, rs, rl)
        pfx = "XXX"
        if (match(m, prefixPat)) { pfx = substr(m, RSTART, RLENGTH) }
        if (!(m in mapping)) {
            # scope the count to the prefix so we can add more without breaking tests
            if (!count[pfx]) { count[pfx] = 1 }
            mapping[m] = count[pfx]
            count[pfx]++
        }
        out = out substr($0, 1, rs - 1) pfx mapping[m]
        $0 = substr($0, rs + rl)
    }
    print out $0
}
'

# normalise machine names
clean_names() {
    awk "$_awk_clean_name"
}

append_package_path() {
    export IDRIS2_PACKAGE_PATH="$IDRIS2_PACKAGE_PATH$SEP$1"
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
    # Use TEST_IDRIS2_LIBS and TEST_IDRIS2_DATA to pass locations for
    # prebuilt libidris2_support and its DATA files.
    export IDRIS2_LIBS="$OLD_PP/lib$SEP$NEW_PP/lib$SEP$TEST_IDRIS2_LIBS"
    export IDRIS2_DATA="$OLD_PP/support$SEP$NEW_PP/support$SEP$TEST_IDRIS2_DATA"

    # Set where to install stuff
    export IDRIS2_PREFIX="$NEW_PREFIX"

    # Save from re-sourcing this file several times
    export PREFIX_CHANGED=1
fi

# Set the most neutral locale for reproducibility
if [ "$OS" = "darwin" ]; then
    export LANG=C LC_CTYPE=UTF-8
else
    export LC_ALL=C.UTF-8
fi

# Remove test directory from output
# Useful for consistency of output between machines
# Usage: run SomeTest.idr | filter_test_dir
filter_test_dir() {
    sed -e 's/\\\{1,2\}\b/\//g' | # Guess at where Windows \ need to be replaced by /
        sed -e "s/$(sed_literal "$test_dir")/__TEST_DIR__/g"
}
