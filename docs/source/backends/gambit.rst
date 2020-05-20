****************************
Gambit Scheme Code Generator
****************************

The Gambit Scheme code generator can be accessed via the REPL command:

::

    Main> :set cg gambit

Ergo, to run Idris programs with this generator, you will need to install
`Gambit Scheme <https://gambitscheme.org>`_. Gambit Scheme is free software,
and available via most pacakge managers.

You can compile an expression ``expr`` of type ``IO ()`` to an executable as
follows, at the REPL:

::

    Main> :c execname expr

...where ``execname`` is the name of the executable file. This will generate
the following:

* An executable binary ``build/exec/execname`` of the program.
* A Gambit Scheme source file ``build/exec/execname.scm``, from which the
  binary is generated.

You can also execute an expression directly:

::

    Main> :exec expr

Again, ``expr`` must have type ``IO ()``. This will generate a temporary
Scheme file, and execute the Gambit interpreter on it.
