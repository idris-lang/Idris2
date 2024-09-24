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


Chez Directives
===============

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

  ::

    $ idris2 --codegen chez --directive extraRuntime=/path/to/extensions.scm -o main Main.idr

* ``--directive lazy=weakMemo``

  Makes all non-toplevel ``Lazy`` and ``Inf`` values to be *weakly* memoised.
  That is, once this expression is evaluated at runtime, it is allowed to not to be recalculated on later accesses
  until memoised value is wiped by a garbage collector.
  Garbage collector is allowed to collect weakly memoised values at its own discretion,
  so when no free memory is available, weakly memoised values are free to be wiped.
  That's why it is safer comparing to full memoisation.

Making a freestanding executable
================================

It's possible to embed the Chez Scheme system and the built Idris2 program into a freestanding executable with `chez-exe <https://github.com/gwatt/chez-exe>`_.

  * Build and install the ``compile-chez-program-tool`` by running the
    configuration script and then make:

    ::

      $ scheme --script gen-config.ss --bootpath <bootpath>

    where ``<bootpath`` is the path to where the Chez Scheme bootfiles (``petite.boot`` and ``scheme.boot``) and ``scheme.h`` are. More
    configuration is described in the chez-exe installation instructions.

  * Invoke ``compile-chez-program``:

    ::

      $ compile-chez-program --optimize-level 3 build/exec/my_idris_prog_app/my_idris_prog.ss

    Note that it can only use the ``.ss``-file and not the ``.so``-file. To
    embed the full Chez Scheme system including the compiler add the ``--full-chez`` option.

  * The finished executable still requires the libidris_support shared
    library. It's possible to also eliminate that dependency by linking with
    it statically.

