********
Pragmas
********

.. role:: idris(code)
    :language: idris

Idris2 supports a number of pragmas (identifiable by the `%` prefix). Some pragmas change compiler behavior
until the behavior is changed back using the same pragma while others apply to the following declaration. A
small niche of pragmas apply directly to one or more arguments instead of the code following the pragma
(like the `%name` pragma described below).

.. note::
    This page is a work in progress. If you know about a pragma that is not described yet, please consider
    submitting a pull request!


``%builtin``
====================

The ``%builtin Natural`` pragma converts recursive/unary representations of natural numbers
into primitive ``Integer`` representations.

This pragma is explained in detail on its own page. For more, see :ref:`builtins`.

``%deprecate``
====================

Mark the following definition as deprecated. Whenever the function is used, Idris will show a deprecation
warning.

.. code-block:: idris

   %deprecate
   foo : String -> String
   foo x = x ++ "!"

   bar : String
   bar = foo "hello"

.. code-block:: none

   Warning: Deprecation warning: Man.foo is deprecated and will be removed in a future version.

You can use code documentation (triple vertical bar `||| docs`) to suggest a strategy for removing the
deprecated function call and that documentation will be displayed alongside the warning.

.. code-block:: idris

   ||| Please use the @altFoo@ function from now on.
   %deprecate
   foo : String -> String
   foo x = x ++ "!"

   bar : String
   bar = foo "hello"

.. code-block:: none

   Warning: Deprecation warning: Man.foo is deprecated and will be removed in a future version.
     Please use the @altFoo@ function from now on.

``%inline``
====================

Instruct the compiler to inline the following definition when it is applied. It is generally best to let the
compiler and the backend you are using optimize code based on its predetermined rules, but if you want to
force a function to be inlined when it is called, this pragma will force it.

.. code-block:: idris

   %inline
   foo : String -> String
   foo x = x ++ "!"

``%noinline``
====================

Instruct the compiler _not_ to inline the following definition when it is applied. It is generally best to let the
compiler and the backend you are using optimize code based on its predetermined rules, but if you want to
force a function to never be inlined when it is called, this pragma will force it.

.. code-block:: idris

   %noinline
   foo : String -> String
   foo x = x ++ "!"

``%name``
====================

Give the compiler some suggested names to use for a particular type when it is asked to generate names for values.
You can specify any number of suggested names; they will be used in-order when more than one is needed for a single
definition.

.. code-block:: idris

   data Foo = X | Y

   %name Foo foo,bar

``%hide``
====================

Hide a definition from imports. This is particularly useful when you are re-definiing functions or types from
a module but still need to import it.

.. code-block:: idris

   module MyNat

   %hide Prelude.Nat
   %hide Prelude.S
   %hide Prelude.Nat

   data Nat = Z | S Nat

You can also hide fixity declarations if you need to redefine your own.

.. code-block:: idris

   module MyNat

   %hide Prelude.Ops.infixl.(+)

   infixr 5 +
