#!/usr/bin/env bash

# quick hack to cope with stack limit when building libs
node --stack-size=80000 $0.js $@
