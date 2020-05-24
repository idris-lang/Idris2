*********************
Racket Code Generator
*********************

The Racket code generator is accessed via a REPL command:

::

    Main> :set cg racket

Alternatively, you can set it via the ``IDRIS2_CG`` environment variable:

::

    $ export IDRIS2_CG=racket

You can compile an expression ``expr`` of type ``IO ()`` to an executable as
follows, at the REPL:

::

    Main> :c execname expr

...where ``execname`` is the name of the executable file. This will generate
the following:

* A shell script ``build/exec/execname`` which invokes the program
* A subdirectory ``build/exec/execname_app`` which contains all the data necessary
  to run the program. This includes the Racket source (``execname.rkt``),
  the compiled Racket code (``execname`` or ``execname.exe`` on Windows)
  and any shared libraries needed for foreign function definitions.

The executable ``execname`` is relocatable to any subdirectory, provided that
``execname_app`` is also in the same subdirectory.

You can also execute an expression directly:

::

    Main> :exec expr

Again, ``expr`` must have type ``IO ()``. This will generate a temporary
executable script ``_tmpracket`` in the ``build/exec`` directory, and execute
that, without compiling to a binary first (so the resulting Racket code is
interpreted).
