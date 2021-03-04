.. _ref-sect-envvars:

*********************
Environment Variables
*********************

Idris 2 recognises a number of environment variables, to decide where to look
for packages, external libraries, code generators, etc. It currently recognises,
in approximately the order you're likely to need them:

* ``EDITOR`` - Sets the editor used in REPL :e command
* ``IDRIS2_CG`` - Sets which code generator to use when compiling programs
* ``IDRIS2_PACKAGE_PATH`` - Lists the directories where Idris2 looks for packages,
  in addition to the defaults (which are under the ``IDRIS2_PREFIX`` and in the
  ``depends`` subdirectory of the current working directory).
  Directories are separated by a ``:``, or a ``;`` on Windows
* ``IDRIS2_PATH`` - Places Idris2 looks for import files, in addition to the
  imports in packages
* ``IDRIS2_DATA`` - Places Idris2 looks for its data files. These are typically
  support code for code generators.
* ``IDRIS2_LIBS`` - Places Idris2 looks for libraries used by code generators.
* ``IDRIS2_PREFIX`` - Gives the Idris2 installation prefix
* ``CHEZ`` - Sets the location of the ``chez`` executable used in Chez codegen
* ``RACKET`` - Sets the location of the ``racket`` executable used in Racket codegen
* ``RACKET_RACO`` - Sets the location of the ``raco`` executable used in Racket codegen
* ``GAMBIT_GSI`` - Sets the location of the ``gsi`` executable used in Gambit codegen
* ``GAMBIT_GSC`` - Sets the location of the ``gsc`` executable used in Gambit codegen
* ``GAMBIT_GSC_BACKEND`` - Sets the ``gsc`` executable backend argument
* ``IDRIS2_CC`` - Sets the location of the C compiler executable used in RefC codegen
* ``CC`` - Sets the location of the C compiler executable used in RefC codegen
* ``NODE`` - Sets the location of the ``node`` executable used in Node codegen
* ``PATH`` - used to search for executables in certain codegens
