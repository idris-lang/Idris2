#!/usr/bin/env sh

sed -e "s|__PWD__|$(pwd)|g" expected.in > expected
