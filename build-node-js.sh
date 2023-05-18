#!/bin/sh

set -e # exit on any error

# build native idris first
# beacuse node js idris executable crashes with Maximum call stack size exceeded when compiling libraries

# wipe out all existing built files
make distclean

# bootstrap with chez scheme
# for now we suppose default chez scheme executable 
make bootstrap SCHEME=chezscheme

# install native idris2
# this will also compile the base libraries as .ttc files and places them properly
make install

# build node js idris 2 executable
$HOME/.idris2/bin/idris2 --build idris2.node.js.ipkg

# make it executable
chmod +x ./build/exec/idris2.node.js

# copy compiled libraries
cp -r $HOME/.idris2/idris2-0.6.0/prelude-0.6.0/2023033100/* build/ttc/2023033100

# copy only the needed files to a directory ready to be distributed
rm -rf build-node-js
mkdir -p build-node-js
cp ./build/exec/idris2.node.js build-node-js/
find build -name '*.ttc' | cpio -pdm build-node-js

# How to use so far:
# cd in the build-node-js directory and run ./idris2.node.js

# Tested so far:
# - run where it was build
# - sent over network to a windows machine and it works (I myself cannot believe it)
# - ./idris2.node.js succesfully opens a repl and executes 1 + 1

# Known limitations so far:
# - to let the nodejs executable locate library files correctly the current working directory must be build-node-js