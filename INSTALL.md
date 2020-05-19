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

Make sure that:

* `$PREFIX/bin` is in your `PATH`
* `$PREFIX/lib` is in your `LD_LIBRARY_PATH` (so that the system knows where
  to look for library support code)


1a: Installing without an existing Idris 2
------------------------------------------

If you *don't* have Idris-2-in-Idris-1 installed, you can build from pre-built
Chez Scheme source, as long as you have Chez Scheme installed. To do this,
enter:

* `make bootstrap SCHEME=chez`

`chez` is the executable name of the Chez Scheme compiler.  You may need to
replace this with the executable for Chez Scheme on your system. This could be
`scheme`, `chezscheme` or `chezscheme9.5` or something else, depending on your
system and the Chez Scheme version.

This builds an Idris 2 compiler from scheme code output from a working Idris 2
compiler (which isn't necessarily up to date, but is up to date enough to
build the current repository). It then rebuilds using the result.

Then to install, type:

* `make install`

If you want to check everything is working, type:

* `make test IDRIS2_BOOT=idris2sh`

(You have to install first, because the test script relies on an existing
Idris 2 installation.)

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

3: Testing
----------

After `make all`, type `make test` to check everything works. This uses the
executable in `./build/exec`.
