.. _operators:

*********
Operators
*********

Idris2 does not have syntax blocs (like in Idris1) or mixfix operators (like in Agda).
Instead, it expands on the ability of infix operators to enable library designers
to write DSL while keeping error messages under control.

Because operators are not linked to function definitions, they are also part of the
file namespacing and follow the same rules as other defintions.

.. warning::
   Operators can and will make some code less legible. Use with taste and caution.
   This document is meant to be mainly used by library authors and advanced users.
   If you are on the fence about using operators, err on the side of caution and
   avoid them.

Basics
======

Before we jump into the fancy features, let us explain how infix operators work
for most users.

When you see an expression


.. code-block:: idris

    1 + n

It means that there is a function ``(+)`` and a *fixity* declaration
in scope. A fixity for this operator looks like this

.. code-block:: idris

    infixl 8 +

It starts with a fixity keyword, you have the choice to use either ``infixl``,
``infixr``, ``infix`` or ``prefix``.

``infixl`` means the operator is left-associative, so that successive applications
of the operator will bracket to the left: ``n + m + 3 + x = (((n + m) + 3) + x)```.
Similarly, ``infixr`` is right-associative, and ``infix`` is non-associative, so the
brackets are mandatory.

The number afterwards indicate the *precedence* of the operator, that is, if it should
be bracketed before, or after, other operators used in the same expression. For example,
we want ``*`` to *take precedence* over ``+`` , because of this, we define it like this:

.. code-block:: idris

    infixl 9 *

This way, the expression ``n + m * x`` is correctly interpreted as ``n + (m * x)``.


Fixity & Precedence Namespacing
===============================

Just like other top-level declarations in the language, fixities can be exported
with the ``export`` access modifier, or kept private with ``private``.

A ``private`` fixity will remain in scope for the rest of the file but will not be
visible to users that import the module. Because fixities and operators are
separate, this does not mean you cannot use the functions that have this operator
name, it merely means that you cannot use it in infix position. But you can use
it as a regular function application using brackets. Let us see what this
looks like

.. code-block:: idris

   module A

   private infixl &&& 8

   -- a binary function making use of our fixity definition
   export
   (&&&) : ...

.. code-block:: idris

   module B

   import A

   main : IO ()
   main = do print (a &&& b) -- won't work
             print ((&&&) a b) -- ok

Private record fixity pattern
-----------------------------

Private fixity declarations are useful in conjuction with records. When
you declare a record with operators as fields, it is helpful to write
them in infix position. However, the compiler will also synthesize a
projection for the field that takes a value of the record as the first
argument, making it unsuitable for use as a binary operator.

.. code-block:: idris


   infixl 7 <@>
   record SomeRelation (a : Type) where
     (<@>) : a -> a -> Type
     compose : (x, y, z : a) -> x <@> y -> y <@> z -> x <@> z

   lteRel : SomeRelation Nat
   lteRel = ...

   natRel : Nat -> Nat -> Type
   natRel x y = (<@>) lteRel x y

What we really want to write is ``natRel x y = <@> x y`` but
``(<@>)`` now has type ``SomeRelation a -> a -> a -> Type``.

The solution is to define a private field with a private fixity
and a public one which relies on proof search to find the appropriate
argument:

.. code-block:: idris

   private infixl 7 <!@>
   export  infixl 7 <@>

   record SomeRelation (a : Type) where
     (<!@>) : a -> a -> Type
     compose : (x, y, z : a) -> x <!@> y -> y <!@> z -> x <!@> z

   export
   (<@>) : (rel : SomeRelation a) => a -> a -> Type
   x <@> y = (<!@>) rel x y

   %hint
   lteRel : SomeRelation Nat
   lteRel = ...

   natRel : Nat -> Nat -> Type
   natRel x y = x <@> y

We define ``(<@>)`` as a projection function with an implicit parameter
allowing it to be used as a binary operator once again.

Private Local definition
------------------------

Private fixity definitions are useful when redefining an operator fixity
in a module. This happens when multiple DSLs are imported as the same time
and you do not want to expose conflicting fixity declarations:

.. code-block:: idris

   module Coproduct

   import Product

   -- mark this as private since we don't want to clash
   -- with the Prelude + when importing the module
   private infixr 5 +

   data (+) : a -> a -> Type where
     ...

   distrib1 : {x, y, z : a} -> x + y + z -> (x + y) + z

Here ``distrib1`` makes explicit use of the operator being defined as
right-associative.

Typebind Operators
==================

Autobind Operators
==================


