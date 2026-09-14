#!/bin/sh

# set -e # exit on any error

IDRIS_2_VERSION="0.8.0"
INSTALL_LOCATION_VARIABLE="INSTALL_LOCATION"
IDRIS_2_DIR="\$$INSTALL_LOCATION_VARIABLE"
DEFAULT_INSTALL_DIR="\$HOME/.idris2"

if [ -z "$FILE_NAME" ]; then
    echo "FILE_NAME is not set."
    exit 1
fi

if [ -z "$CURRENT_BUILD" ]; then
    echo "CURRENT_BUILD is not set."
    exit 1
fi

if ! [ -d "$CURRENT_BUILD" ]; then
    echo "Required assets do not exist."
    exit 1
fi

touch "$FILE_NAME"
echo "#!/bin/sh" > "$FILE_NAME"

# make script exit on any error
echo "set -e" >> "$FILE_NAME"

if [ -z "$BASE64" ]; then
    echo 'PAYLOAD_LINE=$(awk '\''/^__PAYLOAD__/ {print NR + 1; exit}'\'' "$0")' >> "$FILE_NAME"
fi

# add a check for if the user has set an install location
cat <<EOF >> "$FILE_NAME"
if [ -z \$1 ]; then
    $INSTALL_LOCATION_VARIABLE=$DEFAULT_INSTALL_DIR
    echo "No installation directory provided. Defaulting to $IDRIS_2_DIR."

    # make sure default location exists
    mkdir -p $IDRIS_2_DIR
else
    $INSTALL_LOCATION_VARIABLE=\$1
    if ! [ -d "$IDRIS_2_DIR" ]; then
        echo "$IDRIS_2_DIR is not an existing directory."
        exit 1
    fi
fi
EOF

# add a check to look for chez scheme in target environment if using chez
# allow user to also point the script to chez using a variable
# and so also check that they have not done so
if [ -z "$RACKET" ]; then
    cat <<EOF >> "$FILE_NAME"
    if [ -z \$SCHEME ]; then
    # check if 'which chez' is succesful and attempt 'which scheme' if not
        if ! SCHEME=\$(which chez 2>/dev/null); then
            if ! SCHEME=\$(which scheme 2>/dev/null); then
                echo "Chez scheme not found in environment."
                exit 1
            fi
        fi
    fi
    export SCHEME
EOF
fi

# add commands for unpacking
if [ -z "$BASE64" ]; then
    echo "tail -n +\"\$PAYLOAD_LINE\" \"\$0\" | tar -xz -C \"$IDRIS_2_DIR\"" >> "$FILE_NAME"
else
    echo "base64 -d <<'EOF' | tar -xz -C \"$IDRIS_2_DIR\"" >> "$FILE_NAME"
    tar -cz -C "$CURRENT_BUILD" . | base64 >> "$FILE_NAME"
    echo "EOF" >> "$FILE_NAME"
fi

# if installation uses chez then add chez specific parts
if [ -z "$RACKET" ]; then

    # add commands to add compileChez
    cat <<EOF >> "$FILE_NAME"
    echo "(parameterize ([optimize-level 3] [compile-file-message #f]) (compile-program \"$IDRIS_2_DIR/bin/idris2_app/idris2.ss\"))" > "$IDRIS_2_DIR/bin/idris2_app/compileChez"
    echo "(parameterize ([optimize-level 3] [compile-file-message #f]) (compile-program \"idris2.ss\"))" > "$IDRIS_2_DIR/bin/idris2_app/compileChez"
EOF

    # add chez recompilation for version compatibility
    cat <<EOF >> "$FILE_NAME"
    CURRENT="\$PWD"
    cd "$IDRIS_2_DIR/bin/idris2_app"

    # check if versions match
    if [ -f "chez_version" ]; then
        EXPECTED_VERSION=\$(< chez_version)
        AVAILABLE_VERSION=\$("\$SCHEME" --version)

        if [[ "\$AVAILABLE_VERSION" != "\$EXPECTED_VERSION" ]]; then
            echo "Chez version mismatch. Recompiling."
            echo "Expected version: \$EXPECTED_VERSION"
            echo "Available version: \$AVAILABLE_VERSION"

            # if [ -f "$IDRIS_2_DIR/bin/idris2_app/compileChez" ]; then
            if [ -f "compileChez" ]; then
                # sed -e 's,/.*/,,' "$IDRIS_2_DIR/bin/idris2_app/compileChez" > "$IDRIS_2_DIR/bin/idris2_app/recompile"
                sed -e 's,/.*/,,' "compileChez" > "recompile"
                # "\$SCHEME" --script "$IDRIS_2_DIR/bin/idris2_app/recompile"
                "\$SCHEME" --script "recompile"
                # rm -v "$IDRIS_2_DIR/bin/idris2_app/recompile"
                rm -v "recompile"

                # update stored version
                echo "\$AVAILABLE_VERSION" > chez_version
            else
                echo "Not found: $IDRIS_2_DIR/bin/idris2_app/compileChez"
                exit 1
            fi
        fi
    else
        echo "Not found: $IDRIS_2_DIR/bin/idris2_app/chez_version"
        exit 1
    fi
    cd "\$CURRENT"
EOF

fi

# add success message
echo 'echo "Succesfully installed Idris2."' >> "$FILE_NAME"

# add exit
echo "exit 0" >> "$FILE_NAME"

# add payload
if [ -z "$BASE64" ]; then
    echo "__PAYLOAD__" >> "$FILE_NAME"
    tar -czf - -C "$CURRENT_BUILD" . >> "$FILE_NAME"
fi

# make it executable
chmod +x "$FILE_NAME"
