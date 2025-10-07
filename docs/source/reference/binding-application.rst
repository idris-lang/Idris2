
.. _binding:

*********
Binding Application
*********

Binding application allows to overload the syntax of function application to better express the
semantics of dependent types. Take for example the mathematical notation for Sigma-types:
:math:`\Sigma x \in \mathbb{N} . Fin\ x` it binds the variable ``x`` and makes it available in the
scope after the dot. Another example is the mathematical notation for ``forall``:
:math:`\forall x \in \mathbb{N} | p x` it states that for all values ``x`` in the set of natural
number, the property ``p`` holds.

Without any additional syntactic help those two types are only expressible using a lambda:

.. code-block:: idris
    record Sigma (a : Type) (p : a -> Type) where
      fst : a
      snd : p fst

    record Pi (a : Type) (p : a -> Type) where
      fn : (x : a) -> p x

    sigmaExample : Sigma Nat (\n => Vect n Int)

    piExample : Pi Nat (\n => Vect n Int)


Ideally, instead of relying on a lambda, we would like to write something closer to the original
mathematical notation, binding application allows the following syntax:

.. code-block:: idris
    sigmaExample' : Sigma (n : Nat) | Vect n Int

    piExample' : Pi (n : Nat) | Vect n Int

Binding Types
=============

The first way to use binding application is to bind a type to a name. If
we take our ``Sigma`` example again it means that we need to tell the compiler that the type
constructor can be used with binding syntax. We do this by annotating the type declaration with
the ``typebind`` keyword.


.. code-block:: idris
   typebind
   record Sigma (a : Type) (p : a -> Type) where
     constructor MkSigma
     fst : a
     snd : p fst


The type constructor can now be called with this syntax: ``Sigma (n : Nat) | Vect n Int``. And it reads
"Sigma ``n`` of type ``Nat`` such that ``Vect n Int``. This reading is appropriated from the
mathematical notation :math:`\forall x \in \mathbb{N} | p x` which reads the same.
We can also annotate functions with the same keyword, for example the following alias is allowed:

.. code-block:: idris
   typebind
   ∃ : (a : Type) -> (p : a -> Type) -> Type
   ∃ = Sigma

In the implementation of this function we've used the ``Sigma`` type-constructor without any binding
syntax. That is because marking something as binding does not stop them from using them with regular
function application, for example the following is allowed:

.. code-block:: idris
   -- binding syntax from our alias
   s1 : ∃ (n : Nat) | Fin n
   s1 = ...

   -- pointfree notation is allowed
   s2 : Sigma Nat Fin
   s2 = ...

   s3 : (Nat -> Type) -> Type
   s3 = Sigma Nat -- partial application is allowed


We've seen that you can annotate functions and type constructors, you can also annotate data-constructors. For example, to annotate a record constructor add the keyword before the `constructor` keyword:

.. code-block:: idris
   record Container where
     typebind
     constructor MkCont
     goal : Type
     solution : goal -> Type

   ListCont : Container
   ListCont = MkCont (n : Nat) | Fin n

You can also annotate constructors for data:

.. code-block:: idris
   data Desc : Type where
     -- normal constructors
     One : Desc
     Ind : Desc -> Desc

     -- binding data constructor
     typebind
     Sig : (s : Type) -> (s -> Desc) -> Desc

Binding application is a desugaring that takes an input of the form ``expr1 (name : type) | expr2``
and maps it to a program ``expr1 type (\name : Type => expr2)``. Binding application will disambiguate
between binding and non-binding calls for example, the following works:

.. code-block:: idris
   namespace E1
     export
     record Exists (a : Type) (p : a -> Type) where

   namespace E2
     export typebind
     record Exists (a : Type) (p : a -> Type) where

   ok : Exists (n : Nat) | Vect n a


The compiler will automatically pick ``Exists`` from ``E2`` because the other one is not marked as
binding. However, when using regular function application, the call must be disambiguated:

.. code-block:: idris
   failing
     noOK : Exists Nat Fin

   unambiguous : E1.Exists Nat Fin



Binding Arbitrary Values
========================

Sometimes, we still want to using binding application syntax, but we are not binding a type. In those
cases you want to use the ``autobind`` feature to infer the type of the value being bound. The keyword
works in the same places as the ``typebind`` keyword, that is:

On type constructors

.. code-block:: idris
   autobind
   record StringProp : (str : String) -> (String -> Type) -> Type where

   autobind
   data MaybeProp : (m : Maybe a) -> (a -> Type) -> Type where

On data constructor:

.. code-block:: idris

on functions:

.. code-block:: idris
   autobind
   for : (List a) -> (a -> IO ()) -> IO ()
   for ls fn = traverse fn ls >> pure ()


Instead of using ``:`` as a separator, we use ``<-`` and so the last function can be used this way:

.. code-block:: idris
   main : IO ()
   main = for (x <- ['a' .. 'z']) |
              putCharLn x

The desguaring works in a similar way except that the type of the argument in the lambda has to be
inferred. ``expr1 (name <- expr2) | expr3`` desugars to ``expr1 expr2 (\name : ? => expr3)``.

Like typebind, you can use regular function application and partial application with ``autobind``
definitions.
