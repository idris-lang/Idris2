#!/bin/sh
# Fake CC for flag-plumbing tests: record all arguments (one per line) into
# $CC_LOG_FILE, then exit 0.  Produces no real output files.
: "${CC_LOG_FILE:=./cc_calls.log}"
for arg in "$@"; do
    printf '%s\n' "$arg"
done >> "$CC_LOG_FILE"
exit 0
