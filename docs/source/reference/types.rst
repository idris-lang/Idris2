Types, Functions, and Interfaces
================================

The type system in Idris 2 is quite powerful, and is the main feature that sets it apart from simply typed languages like Haskell or OCaml.

There are many ways to construct types, those being members of ``Type``, in Idris.

-------------
Functions
-------------


Function types, formed by ``(x : a) -> b``, are valid types, given that ``a`` and ``b`` are valid types
As shorthand, for non-dependent types, ``a -> b`` is the same as ``(_ : a) -> b``.

In addition, to do simple universal quantification, one can write ``forall x . a``, where ``x`` must be only a name (it can't have a type qualifier).
This is desugared to ``{0 x : _} -> a``.

^^^^^^^^^^^^^
Implicits
^^^^^^^^^^^^^

Implicit function types, those where the value of a parameter can be inferred from the context, can take three forms.
The first of these, ``{x : A} -> B``, forms the basis "basic" implicit types.
That is, ``x`` should be inferred *syntactically*.
This is the equivalent of implicit ``forall`` in Haskell or Rocq, where we might state that ``vectorMap`` on a vector might be:

.. code:: idris

    vectorMap : {n : Nat} -> (a -> b) -> Vect n a -> Vect n b

We would then use ``vectorMap`` as follows:

.. code-block:: idris

    vectorMap f v

or

.. code:: idris

    vectorMap {n = m} f v

These two examples show the power of Idris implicits: while they can be inferred by the compiler, if necessary (or desired) they may be specified by the user

Idris has *two* additional modifiers of implicits, however.
The first, while not that important to the type system of Idris, is *incredibly* useful, and it is the default implicit.
Essentially "regular" implicits only try to figure out the type without adding any extra information.

Default implicits, on the other hand, instead of trying to figure out a value, will instead just use a default, which means that unnecessary "simple" functions are unnecessary in Idris: you just use the default value.

The syntax for default implicits is ``{default val x : a} -> b``, where ``val : a``, which is the default value for ``x``.

The third kind of implicits are auto implicits.
Auto implicits are most useful in proofs, where they differ from regular implicits by there purpose.
Regular implicits try to find a "necessary" match.
``auto`` implicits, on the other hand, look for *any* possible construction of a value.
This is useful for propositions, where we often don't need to reason about the specific value of a type member, merely that it exists.
Essentially, auto implicits are for cases where we want the compiler to have more freedom to infer the value

For instance, if we want to automatically pass a proof through some functions, we use ``auto`` defaults.

.. hint::
    Lowercase names in types are automatically universally quantified in types.
    For instance, ``map : (a -> b) -> List a -> List b`` is transformed into ``map : {0 a : Type} -> {0 b : Type} -> (a -> b) -> List a -> List b`` [#f1]_.
    You can write this signature explicitly, and it will compile the same as the simple version, and in addition you could also have the ``forall`` keyword and wrote this as ``map : forall a . forall b . ((a -> b) -> List a -> List b)``.

    If desired, this behavior can be toggled off by ``%unbound_implicits off`` (and back on by ``%unbound_implicits on``)



^^^^^^^^^^^^^
Quantities
^^^^^^^^^^^^^

Idris 2 uses Quantitative Type Theory (`QTT`_) as its theoretical basis.
In QTT, every function type has an associated multiplicity, ``0``, ``1``, or ω.
These correspond with how many times the given input is "used" in the result type.

Very roughly, ``0`` corresponds to a value "being ignored" or *erased*, a value of ``1`` corresponds to a value being "used" once, or being *one-to-one*, and ω (which, in Idris syntax is omitted) corresponds to a type having an unrestricted number of uses.

Note that this idea of "usage" is not always cut and dry.
For instance, as we saw above, ``{0 a : Type} -> {0 b : Type} -> (a -> b) -> List a -> List b`` is a valid type, despite the fact it uses an erased argument.
This is because erased arguments are only ignored at runtime, however, in the above, the usages of ``a`` and ``b`` are in a type, so they are fine.
In addition, we can alias values without changing their multiplicity, so long as we treat them as the same value.
For instance, if ``1 x : a``, ``let 1 y = x in EXPR`` is valid so long as exactly *one of* ``x`` or ``y`` is used in ``EXPR``.
This is one of many examples of how the quantitative notion of "usage" is not always exactly the same as the intuitive notion of "usage".

The syntax for specifying multiplicity in functions is ``(# x : a) -> B`` (or any variation on such), where ``#`` is the multiplicity.
In addition, we may also declare ``let`` binding with a multiplicity, with the syntax ``let # x : a = val in EXPR`` or ``let # x = val in EXPR``.

.. note::
    "Using" a value of multiplicity 1 changes the multiplicity to 0


---------------------------------------
Interfaces and Implementations
---------------------------------------

.. error::
    Add info on interface constructors

Interfaces are the Idris equivalent of Haskell type-classes.
They are modeled as a lot of sugar on implicit types.
Their syntax is as follows:

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
* For an ``interface`` declaration, ``NAME ARG``, where ``NAME`` is the name of the interface being defined, and all of ``ARGS`` are valid types
* For an ``implementation`` definition, ``NAME ARGS``, where ``NAME`` is a name of a interface, and all of ``ARGS`` are valid types

^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Named dependencies
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

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


^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Determining Parameters
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Idris has an equivalent to Haskell's "functional dependencies".
These are called determining parameters, where a given set of parameters determines another if, there can only be a single valid value given the others.
For instance, ``MonadState s m`` *is* determining, as each ``m`` can only have one state.
To write this, we use the syntax
``interface SPEC | PARAMS``, where ``PARAMS`` are determining.

^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Desguaring and Constructors
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

An interface is desugared roughly as follows:

1. Take the interface, turn it into a record, and make all its methods into arguments to the record
2. Turn every instance of the interface into a definition of the record.
3. For each named one, assign the name to the definition, for each unnamed one, add the ``%hint`` pragma
4. Transform every case of ``f : i a => b`` to ``f : {_ : i' a} -> b``, and pattern match on the implicit argument in the definition.

Given this, it seems natural to ask how we can construct "anonymous" inline instances.
Idris takes this into account, by providing interface constructors.
An interface constructor extends an interface by allowing a ``constructor NAME`` clause in an interface definition, which creates a "interface value" constructor. For instance, the following two implementations are equivalent (given `semigroup`_):

.. code:: idris

    [semiList] {a : Type} -> Semigroup (List a) where
        (<+>) = (++)

and

.. code:: idris

    semiList : {a : Type} -> Semigroup (List a)
    semiList = (MkSemigroup (++))

----------------------
Other Forms
----------------------

The two main ways to declare types at the top level are ``record`` and ``data``

.. note::
    Type synonyms, type families, and the like from Haskell are all just normal functions from ``Type`` to something else.
    In addition, this means that one can have anonymous instances, so, for instance, ``Monad (\x => x)`` is a perfectly valid form.

    Even so, it is in general not a good idea to create such instances

``data`` declares (General) Algebraic Data Types ((G)ADTs).
The Haskell style, simple ADT form is always a statement of the form ``data NAME ARGS = ALT {| ALT}``.
``ARGS`` must be a valid list of names.
In addition, each ``ALT`` must be of the form ``CONS PARAMS`` where each ``CONS`` is either an operator or a name (that will be declared as a constructor).
Finally, each of ``PARAMS`` must be a valid type.

To declare (Agda style) Generalized Algebraic Data Types, we must write ``data NAME : KIND where CONS``.
``KIND`` must be a kind (in Idris there isn't actually distinction between types and kinds) whose tail ultimately ends up returning the type ``Type``.
So, for instance, ``data Vect : (n : Nat) -> Type where ...`` is valid, whilst ``data Vect : forall k. (n : Nat) -> k where ...`` is not.
Each ``CONS`` must be a function declaration, except that the name being defined must start with an uppercase letter and the ultimate return type of it must be a fully applied instance of ``NAME``.

The other way to define top level types, ``record``, is documented in detail on the `records`_ page.

^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Existentials in Types
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While not restricted to types, existentials are so prevalent within types that there usage bears mentioning.
Existentials are always of the form ``_``, ``?`` or ``?NAME``, where ``NAME`` is a valid name.
Named existentials are scoped by *module*, however, they may only exist in one term.

.. caution::

    Existentials are scoped over modules.
    This means that a given hole must have a unique name in a module.

Named existential forms an equivalent to "typed holes", that is, a value to be filled in later.
These can occur in types, although typically occur in generated ones.
Most often, this will occur in usages of generic types, where, for instance, given ``show : {a : Type} -> Show a => a -> String``, we transform the context ``show : {a : Type} -> Show a => a -> String, y = show x |- y : String`` to ``x : ?a, Show ?a |- y : String`` [#f2]_ .

``?`` is similar except, while if ``?a``` cannot be inferred it is made it a typed hole, if ``?`` cannot be inferred, it raises an error

----------------------
Reference
----------------------

.. code-block:: peg

    NameWild = "_" | ?NAME? ;
    Type = "%World" | "type" | NAME | EXISTENTIAL | FunctionType | TERM | "forall" NameWild "." Type ;
    TypeWild = "_" | Type ;
    Mult = "0" | "1" ;
    ImpMod = "default" TERM | "auto" ;
    ParamSpec = NameWild | "(" Mult? NameWild ":" Type ")" | "{" ImpMod? Mult? NameWild ":" Type "}" ;
    Constraint = INTERFACE Type* ;
    FunctionType = ParamSpec "->" Type | Constraint "=>" Type | "forall" Name "." Type
    TupleType = "(" Type "," Type ")"

.. _QTT: https://bentnib.org/quantitative-type-theory.pdf

.. _semigroup: https://www.idris-lang.org/Idris2/prelude/docs/Prelude.Interfaces.html#Prelude.Interfaces.Semigroup

.. [#f1] Assuming ``List`` is in scope

.. [#f2] With many steps omitted for brevity

.. _records: https://idris2.readthedocs.io/en/latest/reference/records.html
