.. _sect-execs:

************************
Compiling to Executables
************************

.. note::

   The documentation for Idris has been published under the Creative
   Commons CC0 License. As such to the extent possible under law, *The
   Idris Community* has waived all copyright and related or neighboring
   rights to Documentation for Idris.

   More information concerning the CC0 can be found online at: http://creativecommons.org/publicdomain/zero/1.0/

Idris 2 (the language) is designed to be independent of any specific code
generator. Still, since the point of writing a program is to be able to run it,
it's important to know how to do so! By default, Idris compiles to executables
via `Chez Scheme <https://www.scheme.com/>`_.

You can compile to an executable as follows, at the REPL:

::

     Main> :c execname expr

...where ``execname`` is the name of the executable file to generate, and
``expr`` is the Idris expression which will be executed. ``expr`` must have
type ``IO ()``. This will result in an executable file ``execname``, in a
directory ``build/exec``, relative to the current working directory.

You can also execute expressions directly:

::

    Main> :exec expr

Again, ``expr`` must have type ``IO ()``.

Finally, you can compile to an executable from the command line by adding
the ``-o <output file>`` option:

::

    $ idris2 hello.idr -o hello

This will compile the expression ``Main.main``, generating an executable
``hello`` (with an extension depending on the code generator) in the
``build/exec`` directory.

There are five code generators provided in Idris 2, and (later) there will be
a system for plugging in new code generators for a variety of targets. The
default is to compile via Chez Scheme, with an alternative via Racket or Gambit.
You can set the code generator at the REPL with the `:set codegen` command,
or via the `IDRIS2_CG` environment variable.

.. toctree::
   :maxdepth: 1

   chez
   racket
   gambit
   javascript
   refc
   custom
   backend-cookbook

There are also external code generators that aren't part of the main Idris 2
repository and can be found on Idris 2 wiki:

`External backends <https://github.com/idris-lang/Idris2/wiki/External-backends>`_
