.. _app-index:

################################
Structuring Idris 2 Applications
################################

A tutorial on structuring Idris 2 applications using ``Control.App``.

.. note::

   The documentation for Idris has been published under the Creative
   Commons CC0 License. As such to the extent possible under law, *The
   Idris Community* has waived all copyright and related or neighboring
   rights to Documentation for Idris.

   More information concerning the CC0 can be found online at: http://creativecommons.org/publicdomain/zero/1.0/

.. toctree::
   :maxdepth: 1

Idris applications have ``main : IO ()`` as an entry point.  A type ``IO a`` is
a description of interactive actions which produce a value of type ``a``. This
is fine for primitives, but ``IO`` does not support exceptions so we have to be
explicit about how an operation handles failure. Also, if we do
want to support exceptions, we also want to explain how exceptions and linearity
(see Section :ref:`sect-multiplicities`) interact.

In this tutorial, we describe a parameterised type ``App`` and a related
parameterised type ``App1``, which together allow us to structure larger
applications, taking into account both exceptions and linearity. The aims of
``App`` and ``App1`` are that they should:

* make it possible to express what interactions a function does, in its type,
  without too much notational overhead.
* have little or no performance overhead compared to writing in *IO*.
* be compatible with other libraries and techniques for describing effects,
  such as algebraic effects or monad transformers.
* be sufficiently easy to use and performant that it can be the basis of
  *all* libraries that make foreign function calls, much as *IO*
  is in Idris 1 and Haskell
* be compatible with linear types, meaning that they should express whether a
  section of code is linear (guaranteed to execute exactly once without
  throwing an exception) or whether it might throw an exception.

We begin by introducing ``App``, with some small example
programs, then show how to extend it with exceptions, state, and other
interfaces.

[To be continued...]
