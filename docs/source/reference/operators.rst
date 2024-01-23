.. _operators:

*********
Operators
*********

Idris2 does not have syntax blocs (like in Idris1) or mixfix operators (like in Agda).
Instead, it expands on the abilities of infix operators to enable library designers
to write Domain Specific Languages (DSLs) while keeping error messages under control.

Because operators are not linked to function definitions, they are also part of the
file namespacing and follow the same rules as other defintions.

.. warning::
   Operators can and will make some code less legible. Use with taste and caution.
   This document is meant to be mainly used by library authors and advanced users.
   If you are on the fence about using operators, err on the side of caution and
   avoid them.

Basics
======

Before we jump into the fancy features, let us explain how operators work
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
brackets are mandatory. Here, we chose for ``+`` to be left-associative, hence ``infixl``.

The number after the fixity indicate the *precedence level* of the operator, that is, if it should
be bracketed before, or after, other operators used in the same expression. For example,
we want ``*`` to *take precedence* over ``+`` we write:

.. code-block:: idris

    infixl 9 *

This way, the expression ``n + m * x`` is correctly interpreted as ``n + (m * x)``.

Fixities declarations are optional and only change how a file is parsed, but you can
use any function defined with operator symbols with parenthesis around it:

.. code-block:: idris

   -- those two are the same
   n + 3
   (+) n 3

Because fixities are separated from the function definitions, a single operator
can have 0 or multiple fixity definitions. In the next section we explain how to
deal with multiple fixity definitions.

Fixity & Precedence Namespacing
===============================
Sometimes it could be that you need to import two libraries that export
conflicting fixities. If that is the case, the compiler will emit a warning
and pick one of the fixities to parse the file. If that happens, you should
hide the fixity definitions that you do not wish to use. For this, use the
``%hide`` directive, just like you would to hide a function definition, but
use the fixity and the operator to hide at the end. Let's work through an
example:

.. code-block:: idris

   module A
   export infixl 8 -

.. code-block:: idris

   module B
   export infixr 5 -

.. code-block:: idris

   module C

   import A
   import B

   test : Int
   test = 1 - 3 - 10

This program will raise a warning on the last line of module ``C`` because
there are two conflicting fixities in scope, should we parse the expression
as ``(1 - 3) - 10`` or as ``1 - (3 - 10)``? In those cases, you can hide
the extra fixity you do not wish to use by using ``%hide``:

.. code-block:: idris

   module C

   import A
   import B

   %hide A.infixl.(-)

   test : Int
   test = 1 - 3 - 10 -- all good, no error

In which case the program will be parsed as ``1 - (3 - 10)`` and not emit
any errors.

Export modifiers on fixities
----------------------------

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

In what follows we have two examples of programs that benefit from
declaring a fixity ``private`` rather than ``export``.

Private record fixity pattern
-----------------------------

Private fixity declarations are useful in conjuction with records. When
you declare a record with operators as fields, it is helpful to write
them in infix position. However, the compiler will also synthesize a
projection function for the field that takes as first argument the
a value of the record to project from. This makes using the operator
as a binary infix operator impossible, since it now has 3 arguments.

.. code-block:: idris


   infixl 7 <@>

   record SomeRelation (a : Type) where
     (<@>) : a -> a -> Type
     -- we use the field here in infix position
     compose : {x, y, z : a} -> x <@> y -> y <@> z -> x <@> z

   lteRel : SomeRelation Nat
   lteRel = ...

   -- we want to use <@> in infix position here as well but we cannot
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
     compose : {x, y, z : a} -> x <!@> y -> y <!@> z -> x <!@> z

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

In dependently-typed programming, we have the ability define types which
first argument is a type and the second is a lambda using the first argument
as it's type. A typical example of this is the dependent linear arrow:

 .. code-block:: idris

    infixr 0 =@
    0 (=@) : (x : Type) -> (x -> Type) -> Type
    (=@) x f = (1 v : x) -> f v


However, we cannot use as is because the second argument is
a lambda, and writing out any value using this operator will look a bit awkward:

.. code-block:: idris

   linearSingleton : Nat =@ (\x => Singleton x)
   linearSingleton = ...

What we really want to write, is something like the dependent arrow ``->`` but
for linear types:

.. code-block:: idris

   linearSingleton : (x : Nat) =@ Singleton x
   linearSingleton = ...

The above syntax is allowed if the operator is declared as ``typebind``. For
this, simply add the ``typebind`` keyword in front of the fixity declaration.

.. code-block:: idris

   typebind infixr 0 =@

``typebind`` is a modifier like ``export`` and both can be used at the same time.


An operator defined as ``typebind`` cannot be used in regular position anymore,
writing ``Nat =@ (\x => Singleton x)`` will raise an error.

This new syntax is purely syntax sugar and converts any instance of
``(name : type) op expr`` into ``type op (\name : type => expr)``

Because of its left-to-right binding structure, typebind operators can
only ever be ``infixr`` with precedence 0.


Autobind Operators
==================

Typebind operators allow to bind a *type* on the left side of an operator, but
sometimes, there is no dependency between the first argument, and the expression
on the right side of the operator. For those case, we use ``autobind``.

An example of this is a DSL for a dependently-typed programming language
where the constructor for ``Pi`` takes terms on the left and lambdas on the right:

.. code-block:: idris

    VPi : Value -> (Value -> Value) -> Value

    sig : Value
    sig = VPi VStar                 (\fstTy -> VPi
          (VPi fstTy (const VStar)) (\sndTy -> VPi
          fstTy                     (\val1 -> VPi
          (sndTy `vapp` val1)       (\val2 ->
          VSigma fstTy sndTy)))))

We would like to use a custom operator to build values using ``VPi``, but its
signature does not follow the pattern that ``typebind`` uses. Instead, we use
``autobind`` to tell the compiler that the type of the lambda is not given
by the first argument. For this we use ``:=`` instead of ``:``:

.. code-block:: idris

    autobind infixr 0 =>>
    (=>>) : Value -> (Value -> Value) -> Value
    (=>>) = VPi


    sig : Value
    sig =
        (fstTy := VStar) =>>
        (sndTy := (_ := fstTy) =>> VStar) =>>
        (val1 := fstTy) =>>
        (val2 := sndTy `vapp` val1) =>>
        VSgima fstTy sndTy

This new syntax is much closer to what the code is meant to look like for users
accustomed to dependently-typed programming languages.

More technically, any ``autobind`` operator is called with the syntax
``(name := expr) op body`` and is desugared into ``expr op (\name : ? => body)``.
If you want, or need, to give the type explicitly, you can still do so by using
the full syntax: ``(name : type := expr) op body`` which is desugared into
``expr op (\name : type => body)``.

Like ``typebind``, ``autobind`` operators cannot be used as regular operators anymore
, additionally an ``autobind`` operator cannot use the ``typebind`` syntax either.
