Trying to boostrap, this complains for missing .ss files in contrib. Can't understand why.

make distclean && \
make bootstrap IDRIS2_APP_IPKG=idris2.node.js.ipkg SCHEME=chezscheme && \
make install IDRIS2_APP_IPKG=idris2.node.js.ipkg

---

Native build, then nodejs exec only, this complains for missing prelude module.
Loggin at "nsToPath" the produced nodejs exec only has ["build/ttc/2023033100/Prelude.ttc", "2023033100/Prelude.ttc"]
while the same with the native exec has also the PREFIX paths

make distclean && \
make bootstrap SCHEME=chezscheme && \
make install && \
make idris2-exec IDRIS2_APP_IPKG=idris2.node.js.ipkg SCHEME=chezscheme && \
make install-idris2 IDRIS2_APP_IPKG=idris2.node.js.ipkg

