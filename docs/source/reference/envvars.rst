.. _ref-sect-envvars:

*********************
Environment Variables
*********************

Idris 2 recognises a number of environment variables, to decide where to look
for packages, external libraries, code generators, etc. It currently recognises,
in approximately the order you're likely to need them:

* ``EDITOR`` - Editor used in REPL ``:e`` command.
* ``PREFIX`` - Default way to set the Idris2 installation prefix.
* ``IDRIS2_PREFIX`` - Alternative way to set the Idris2 installation prefix.
* ``IDRIS2_PATH`` - Directories where Idris2 looks for import files, in addition
  to the imports in packages
* ``IDRIS2_PACKAGE_PATH`` - Directories where Idris2 looks for Idris 2 packages,
  in addition to the defaults (which are under the ``IDRIS2_PREFIX`` and in the
  ``depends`` subdirectory of the current working directory).
  Directories are separated by a ``:`` on MacOS and \*NIX systems, or a ``;`` on
  Windows
* ``IDRIS2_DATA`` - Directories where Idris2 looks for data files. These are
  typically support code for code generators.
* ``IDRIS2_LIBS`` - Directories where Idris2 looks for libraries (for code
  generation).
* ``IDRIS2_CG`` - Codegen backend.
* ``IDRIS2_INC_CGS`` - Code generators to use (comma separated) when compiling modules incrementally.
* ``CHEZ`` - Chez backend: location of the ``chez`` executable.
* ``RACKET`` - Racket backend: location of the ``racket`` executable.
* ``RACKET_RACO`` - Racket backend: location of the ``raco`` executable.
* ``GAMBIT_GSI`` - Gambit backend: location of the ``gsi`` executable.
* ``GAMBIT_GSC`` - Gambit backend: location of the ``gsc`` executable.
* ``GAMBIT_GSC_BACKEND`` - Gambit backend: arguments passed to ``gsc``.
* ``IDRIS2_CC`` - RefC backend: location of the C compiler executable.
* ``IDRIS2_CFLAGS`` - RefC backend: C compiler flags.
* ``IDRIS2_CPPFLAGS`` - RefC backend: C preprocessor flags.
* ``IDRIS2_LDFLAGS`` - RefC backend: C linker flags.
* ``CC`` - RefC backend: C compiler executable (IDRIS2_CC takes precedence).
* ``CFLAGS`` - RefC backend: C compiler flags (IDRIS2_CFLAGS takes precedence).
* ``CPPFLAGS`` - RefC backend: C preprocessor flags (IDRIS2_CPPFLAGS takes precedence).
* ``LDFLAGS`` - RefC backend: C linker flags (IDRIS2_LDFLAGS takes precedence).
* ``NODE`` - NodeJS backend: ``node`` executable.
* ``PATH`` - PATH variable is used to search for executables in certain
  codegens.
* ``NO_COLOR`` - Instruct Idris not to print colour to stdout. Passing the
  --colour/--color option will supersede this environment variable.

