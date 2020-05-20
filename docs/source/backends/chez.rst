**************************
Chez Scheme Code Generator
**************************

The Chez Scheme code generator is the default, or it can be accessed via a REPL
command:

::

    Main> :set cg chez

By default, therefore, to run Idris programs you will need to install
`Chez Scheme <https://www.scheme.com/>`_. Chez Scheme is open source, and
available via most OS package managers.

You can compile an expression ``expr`` of type ``IO ()`` to an executable as
follows, at the REPL:

::

    Main> :c execname expr

...where ``execname`` is the name of the executable file. This will generate
the following:

* A shell script ``build/exec/execname`` which invokes the program
* A subdirectory ``build/exec/execname_app`` which contains all the data necessary
  to run the program. This includes the Chez Scheme source (``execname.ss``),
  the compiled Chez Scheme code (``execname.so``) and any shared libraries needed
  for foreign function definitions.

The executable ``execname`` is relocatable to any subdirectory, provided that
``execname_app`` is also in the same subdirectory.

You can also execute an expression directly:

::

    Main> :exec expr

Again, ``expr`` must have type ``IO ()``. This will generate a temporary
executable script ``_tmpchez`` in the ``build/exec`` directory, and execute
that.

Chez Scheme is the default code generator, so if you invoke ``idris2`` with the
``-o execname`` flag, it will generate an executable script
``build/exec/execname``, again with support files in ``build/exec/execname_app``.
