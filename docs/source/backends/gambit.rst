****************************
Gambit Scheme Code Generator
****************************

The Gambit Scheme code generator can be accessed via the REPL command:

::

    Main> :set cg gambit

Alternatively, you can set it via the ``IDRIS2_CG`` environment variable:

::

    $ export IDRIS2_CG=gambit

To run Idris programs with this generator, you will need to install
`Gambit Scheme <https://gambitscheme.org>`_. Gambit Scheme is free software,
and available via most package managers.

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


Gambit Directives
=================

* ``--directive extraRuntime=<path>``

  Embed Scheme source from ``<path>`` directly into generated output. Can be specified more than
  once, in which case all given files will be included in the order specified.

  .. code-block:: scheme

    ; extensions.scm
    (define (my-mul a b)
      (* a b))


  .. code-block:: idris

    -- Main.idr
    %foreign "scheme:my-mul"
    myMul : Int -> Int -> Int

  .. code-block:: shell

    $ idris2 --codegen gambit --directive extraRuntime=/path/to/extensions.scm -o main Main.idr

* ``--directive C``

  Compile to C. With this directive, gambit will generate a `.c` file instead of an executable.

  .. code-block:: shell

    $ idris2 --codegen gambit --directive C -o main.c Main.idr

Gambit Environment Configurations
=================================

* ``GAMBIT_GSC_BACKEND``

  The ``GAMBIT_GSC_BACKEND`` variable controls which C compiler Gambit will use during compilation. E.g. to use clang:

  ::

    $ export GAMBIT_GSC_BACKEND=clang

  Gambit version 4.9.4 or newer supports the ``-cc`` option, which configures
  the compiler backend Gambit will use to build the binary.
