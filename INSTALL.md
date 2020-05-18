Installing
==========

Requirements: Chez Scheme (with threading support) and bash. On a Mac, you
will need to install `coreutils` to have access to `realpath` - you can
do this with `brew install coreutils`.

0: Set the PREFIX
-----------------

* Change the `prefix` in `config.mk`. The default is to install in
  `$HOME/.idris2sh`

If you have an existing Idris 2, go to step 1b. Otherwise, read on...

1a: Installing without an existing Idris 2
------------------------------------------

If you *don't* have  Idris-2-in-Idris-1 installed, you can still build a
bootstrapping compiler, as long as you have Chez Scheme installed. This is a
bit more fiddly than if you have Idris 2 installed (for the moment - it should
be scriptable) but you only have to do it once.

To begin, enter:

* `make init-bootstrap SCHEME=chez`

(`chez` is the executable name of the Chez Scheme compiler.  You may need to
replace this with the executable for Chez Scheme on your system. This could be
`chez`, `chezscheme` or `chezscheme9.5` or something else, depending on your
system and the Chez Scheme version).

This builds an Idris 2 compiler from scheme code output from a working Idris 2
compiler (which isn't necessarily up to date, but is up to date enough to
build the current repository).

Then, to build the libraries using this generated compiler, again using your
local variant for `chez`.

* `make libs SCHEME=chez`
* `make install SCHEME=chez`

At this point, check that `$PREFIX/bin` is in your `PATH`.

Then, go to the Self-hosting step below, but you'll also need to add
`SCHEME=chez` (with the appropriate name for `chez`) so that the bootstrapping
script knows where to look.  That is:

* `rm -rf build` -- clean the build artefacts
* `make all IDRIS2_BOOT=idris2sh SCHEME=chez`
* `make install`

1b: Installing with an existing Idris 2
---------------------------------------

If you have Idris-2-in-Idris-1 installed: 

* `make all && make install`

2: Self-hosting step
--------------------

Then, to build from the newly installed `idris2sh`, assuming that `idris2sh`
is in your `PATH`.

* `make clean` -- to make sure you're building everything with the new version
* `make all IDRIS2_BOOT=idris2sh && make install`

For amusement, try using `time` on the above. I get about 3m for installing
from `idris2`, and about 1m45 for installing from `idris2sh`.
