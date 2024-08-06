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


Racket Directives
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

  .. code-block::

    $ idris2 --codegen chez --directive extraRuntime=/path/to/extensions.scm -o main Main.idr

* ``--directive lazy=weakMemo``

  Makes all non-toplevel ``Lazy`` and ``Inf`` values to be *weakly* memoised.
  That is, once this expression is evaluated at runtime, it is allowed to not to be recalculated on later accesses
  until memoised value is wiped by a garbage collector.
  Garbage collector is allowed to collect weakly memoised values at its own discretion,
  so when no free memory is available, weakly memoised values are free to be wiped.
  That's why it is safer comparing to full memoisation.
