`
make distclean && \
make bootstrap SCHEME=chezscheme && \
make install && \
mkdir -p build/ttc/2023033100 && \
cp -r ~/.idris2/idris2-0.6.0/*/2023033100/* build/ttc/2023033100 && \
~/.idris2/bin/idris2 --build idris2.node.ipkg && \
node build/exec/idris2.js --codegen node Dumb.idr -o Dumb.js && \
node build/exec/idris2.js
`
