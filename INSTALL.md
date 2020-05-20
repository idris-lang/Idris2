Installing
==========

The easiest way to install is via the existing generated Scheme code. The
requirements are:

* A Scheme compiler; either Chez Scheme (default), or Racket
* `bash`, with `realpath`. On Linux, you probably already have this. On
  a Mac, you can install this with `brew install coreutils`.

On Windows, it has been reported that installing via `MSYS2` works
(https://www.msys2.org/). On Raspberry Pi, you can bootstrap via Racket.

By default, code generation is via Chez Scheme. You can use Racket instead,
by passing `CG=racket` to `make` for the commands below.

[Note: a couple of tests are currently known to fail when installing via
Racket. This will be addressed soon!]

1: Set the PREFIX
-----------------

* Change the `prefix` in `config.mk`. The default is to install in
  `$HOME/.idris2sh`

If you have an existing Idris 2, go to step 1b. Otherwise, read on...

Make sure that:

* `$PREFIX/bin` is in your `PATH`
* `$PREFIX/lib` is in your `LD_LIBRARY_PATH` (so that the system knows where
  to look for library support code)

2: Installing without an existing Idris 2
------------------------------------------

If you *don't* have Idris-2-in-Idris-1 installed, you can build from pre-built
Chez Scheme source, as long as you have Chez Scheme installed (or,
alternatively, Racket). To do this, enter one of the following:

* `make bootstrap SCHEME=chez`
* `make bootstrap-racket`

`chez` is the executable name of the Chez Scheme compiler.  You may need to
replace this with the executable for Chez Scheme on your system. This could be
`scheme`, `chezscheme` or `chezscheme9.5` or something else, depending on your
system and the Chez Scheme version.

This builds an Idris 2 compiler from scheme code output from a working Idris 2
compiler (which isn't necessarily up to date, but is up to date enough to
build the current repository). It then rebuilds using the result, and runs
the tests.

If all is well, to install, type:

* `make install`

(Alternative 2: Installing with an existing Idris 2)
----------------------------------------------------

If you have [Idris-2-in-Idris-1](https://github.com/edwinb/Idris2-boot)
installed: 

* `make all && make install`

3: (Optional) Self-hosting step
-------------------------------

As a final step, you can rebuild from the newly installed Idris 2 to verify
that everything has worked correctly.  Assuming that `idris2sh` is in your
`PATH`.

* `make clean` -- to make sure you're building everything with the new version
* `make all IDRIS2_BOOT=idris2sh && make install`

4: Running tests
----------------

After `make all`, type `make test` to check everything works. This uses the
executable in `./build/exec`.
