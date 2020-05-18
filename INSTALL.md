Installing
==========

Requirements: Chez Scheme (with threading support) and bash. On a Mac, you
will need to install `coreutils` to have access to `realpath` - you can
do this with `brew install coreutils`.

0: Fix hard coded prefix (sorry)
--------------------------------

This isn't easily configurable yet - I will deal with it soon. So, before
you start:

* Change the `prefix` which is currently hard coded in `Idris.Main`.

1a: Installing without an existing Idris 2
------------------------------------------

If you *don't* have  Idris-2-in-Idris-1 installed, you can still build a
bootstrapping compiler, as long as you have Chez Scheme installed. This is a
bit more fiddly than if you have Idris 2 installed (for the moment) but you
only have to do it once.

To begin, enter:

* `make init-bootstrap SCHEME=scheme`

(`scheme` is the executable name of the Chez Scheme compiler.  You may need to
replace this with the executable for Chez Scheme on your system. This could be
`chez`, `chezscheme` or `chezscheme9.5` or something else, depending on your
system and the Chez Scheme version).

This builds an Idris 2 compiler from scheme code output from a working Idris 2
compiler (which isn't necessarily up to date, but is up to date enough to
build the current repository).

Then, to build Idris 2 (again using your local variant for `scheme`)

* `make libs IDRIS2_BOOT=bootstrap/idris2-boot SCHEME=scheme`
* `make all IDRIS2_BOOT=bootstrap/idris2-boot SCHEME=scheme`
* `make install`

1b: Installing with an existing Idris 2
---------------------------------------

If you have Idris-2-in-Idris-1 installed: 

* `make all && make install`

2: Self-hosting step
--------------------

Then, to build from the newly installed `idris2sh`

* `make clean` -- to make sure you're building everything with the new version
* `make all IDRIS_BOOT=idris2sh && make install`

For amusement, try using `time` on the above. I get about 3m for installing
from `idris2`, and about 1m45 for installing from `idris2sh`.
