`make distclean && make bootstrap=chezscheme && make install && idris2 --build idris2.node.ipkg && cp build/exec/idris2.js ~/.idris2/bin/idris.js && node ~/.idris2/bin/idris.js --codegen node Dumb.idr -o Dumb
`
