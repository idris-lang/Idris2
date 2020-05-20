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

There are three code generators provided in Idris 2, and (later) there will be
a system for plugging in new code generators for a variety of targets. The
default is to compile via Chez Scheme, with an alternative via Racket or Gambit.

.. toctree::
   :maxdepth: 1

   chez
   racket
   gambit

