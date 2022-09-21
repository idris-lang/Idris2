#!/usr/bin/env sh

sed -e "s|__PWD__|${MY_PWD}|g" expected.in >expected
