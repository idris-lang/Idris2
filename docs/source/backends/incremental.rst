***************************
Incremental Code Generation
***************************

By default, Idris 2 is a whole program compiler - that is, it finds all the
necessary function definitions and compiles them only when you build an
executable. This gives plenty of optimisation opportunities, but can also
be slow for rebuilding. However, if the backend supports it, you can build
modules and executables *incrementally*. To do so, you can either:

1. Set the ``--inc <backend>`` flag at the command line, for each backend
   you want to use incrementally.
2. Set the ``IDRIS2_INC_CGS`` environment variable with a comma separated list
   of backends to use incrementally.

At the moment, only the Chez backend supports incremental builds.

Building modules incrementally
==============================

If either of the above are set, building a module will produce compiled binary
code for all of the definitions in the module, as well as the usual checked
TTC file. e.g.:

::

    $ idris2 --inc chez Foo.idr
    $ IDRIS2_INC_CGS=chez idris2 Foo.idr

On successful type checking, each of these will produce a Chez Scheme file
(``Foo.ss``) and compiled code for it (``Foo.so``) as well as the usual
``Foo.ttc``, in the same build directory as ``Foo.ttc``.

In incremental mode, you will see a warning for any holes in the module,
even if those holes will be defined in a different module.

Building executables incrementally
==================================

If either ``--inc`` is used or ``IDRIS2_INC_CGS`` is set, compiling to
an executable will attempt to link all of the compiled modules together,
rather than generating code for all of the functions at once. For this
to work, all the imported modules *must* have been built with incremental
compilation for the current back end (Idris will revert to whole program
compilation if any are missing, and you will see a warning.)

Therefore, all packages used by the executable must also have been built
incrementally for the current back end. The ``prelude``, ``base``,
``contrib``, ``network`` and ``test`` packages are all built with
incremental compilation support for Chez by default.

When switching between incremental and whole program compilation, it is
recommended that you remove the ``build`` directory first. This is
particularly important when switching to incremental compilation, since there
may be stale object files that Idris does not currently detect!


Overriding incremental compilation
==================================

The ``--whole-program`` flag overrides any incremental compilation settings
when building an executable.

Performance note
================

Incremental compilation means that executables are generated much quicker,
especially when only a small proportion of modules have changed. However,
it means that there are fewer optimisation opportunities, so the resulting
executable will not perform as well. For deployment, ``--whole-program``
compilation is recommended.


