Types, Functions, and Interfaces
================================

The type system in Idris 2 is quite powerful, and is the main feature that sets it apart from simply typed languages like Haskell or OCaml.

There are many ways to construct types, those being members of ``Type``, in Idris.

-------------
Functions
-------------

Function types, formed by ``(x : A) -> B``, are valid types, given that ``A`` is a valid type *or* kind and ``B`` is a valid type *or* kind. 
As shorthand, for non-dependent types, ``A -> B`` is shorthand for ``(_ : A) -> B``.

^^^^^^^^^^^^^
Implicits
^^^^^^^^^^^^^

Implicit function types, those where the value of a parameter can be inferred from the context, can take three forms.
The first of these, ``{x : A} -> B``, forms the basis "basic" implicit types. 
That is, ``x`` should be inferred *syntactically*. 
This is the equivalent of implicit ``forall`` in Haskell or Rocq, where we might state that ``vectorMap`` on a vector might be

.. code:: idris

    vectorMap : {n : Nat} -> (a -> b) -> (Vect n a) -> (Vect n b)

We would then use ``vectorMap`` as follows: 

.. code-block:: idris

    vectorMap f v

or

.. code:: idris

    vectorMap {n = m} f v

These two examples show the power of Idris implicits: while they can be inferred by the compiler, if necessary (or desired) they may be specified by the user

.. tip:: 
    Idris *not have* a ``forall`` keyword, unlike Haskell. 
    To get the equivalent of ``forall (x : k). A``, we use ``{x : k} -> A``. 
    Not only is this more elegant, it more accurately highlights the connection between universal quantification, implication, and functions

Idris has a *two* more types of implicits, however.
The first, while not that important to the type system of Idris, is *incredibly* useful, and it is the default implicit.
Essentially "regular" implicits only try to figure out the type without adding any extra information.

Default implicits, on the other hand, instead of trying to figure out a value, will instead just use a default, which means that unnecessary "simple" functions are unnecessary in Idris: you just use the default value.

The syntax for default implicits is ``{default val x : A} -> B``, where ``val : A``, which is the default value for ``x``.

The third kind of default are auto defaults.
Auto defaults are most useful in proofs, where they differ from regular defaults by irrelevance.
That is, a regular default will never initiate *anything* that cannot otherwise be initiated, while an ``auto`` default will not change anything outside of the input that cannot be initiated.

For instance, if we want to automatically pass a proof through some functions, we use ``auto`` defaults.

.. warning::
    If you want to use a type name to specify a value in Idris, you *cannot* merely use it as an implicit.
    This is because, as stated before, instead of ``forall``'s we have implicits. 
    This means that if you want to use a type variable, say ``a`` in ``castOne : Cast a b => a -> [b]`` in the function, you must explicitly take it as an argument, e.g ``castOne : {a : Type} -> Cast a b => a -> [b]``, and then use it as ``castOne {a} x``

^^^^^^^^^^^^^
Quantities
^^^^^^^^^^^^^

Function types may also give quantities to their arguments.
These are either ``0``, ``1``, or nothing (many), which are all placed before a named parameter, so, we have ``(# x : A)``.
A value with a multiplicity of zero (erased) must only be used in the type signature (i.e, a Haskell type variable).
A value with a multiplicity of one (linear) must be used exactly once in the definition of the value.

---------------------------------------
Interfaces and Implementations
---------------------------------------

Interfaces are the Idris equivalent of Haskell type-classes.
They are modeled as a lot of sugar on implicit types.
There syntax is as follows:

.. code:: idris

    interface SPEC where
        DEFS

and for implementations

.. code:: idris

    implementation SPEC where 
        DEFS

which can also be written as 

.. code:: idris

    SPEC where 
        DEFS

in addition, we can create "named instances" as 

.. code:: idris

    [INAME] implementation SPEC where 
        DEFS

which can also be written as 

.. code:: idris

    [INAME] SPEC where 
        DEFS


Where ``SPEC`` must be one of the following

* ``... -> SPEC``, such that this would be valid type, and such that ``SPEC`` is itself a valid form
* ``... => SPEC``, similar
* For an ``interface`` deceleration, ``NAME ARG``, where ``NAME`` is the name of the interface being defined, and all of ``ARGS`` are valid types
* For an ``implementation`` definition, ``NAME ARGS``, where ``NAME`` is a name of a interface, and all of ``ARGS`` are valid types

^^^^^^^^^^^^^^^^^^^
Named dependencies
^^^^^^^^^^^^^^^^^^^

There are actually two more ways we can specify instances, those being

.. code:: idris

    [INAME] implementation SPEC using DEP where 
        DEFS

which can also be written as 

.. code:: idris

    [INAME] SPEC using DEP where 
        DEFS


These arise in cases like ``Monoid Int``, where we might have the following code 

.. code:: idris 

    [MultSemi] Semigroup Int where 
        (<+>) = (*)
    [AddSemi] Semigroup Int where 
        (<+>) = (+)
    [MultMonoid] Monoid Int using MultSemi where
        neutral = 1
    [AddMonoid] Monoid Int using AddSemi where 
        neutral = 0

^^^^^^^^^^^^^
Desguaring
^^^^^^^^^^^^^

An interface is desugared roughlt as follows:

1. Take the interface, turn it into a record, and make all its methods into arguements to the record
2. Turn every instance of the interface into a definition of the record, and add the  
