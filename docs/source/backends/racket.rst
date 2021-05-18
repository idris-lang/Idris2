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

Racket Variant
==============

Variable `RACKET_VARIANT` is used to set the proper Racket variant that you want to use in
code generation. For example, you may want to use Chez Scheme by setting it to
`RACKET_VARIANT=cs`, similar to `3m` (the default variant before Racket v8.0).
In addition, a `debug` option is available to configure `raco exe` to `raco exe --3m --gui`.
See [there](https://github.com/NixOS/nixpkgs/issues/11698).
