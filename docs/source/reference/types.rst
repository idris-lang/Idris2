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

Implicit arguments, can take three forms.
The first one, ``{x : a} -> b`` is the most basic form of implicit arguments, that is
 ``x`` should be inferred *syntactically*.
This is the equivalent of implicit ``forall`` in Haskell or Rocq, where we might state that ``vectorMap`` on a vector might be:

.. code:: idris

    vectorMap : {n : Nat} -> (a -> b) -> Vect n a -> Vect n b

We would then use ``vectorMap`` as follows:

.. code-block:: idris

    vectorMap f v

or

.. code:: idris

    vectorMap {n = m} f v

These two examples show the power of Idris implicits: while they can be inferred by the compiler, if necessary (or desired) they may be specified by the user.

The second form of implicits arguments is the default implicit.
Essentially "regular" implicits only try to figure out the type without adding any extra information.
Where "regular" implicits only try to resolve the type without adding any extra information, default implicit arguments, will instead use a default value when the value cannot be resolved syntactically.

This is *incredibly* useful to avoid repeating the same function definition multiple times with a different set of arguments.
The most common case can be given via a default implicit and the other uses can give the argument by name.
The syntax for default implicits is ``{default val x : a} -> b``, where ``val : a``, which is the default value for ``x``.

The third kind of implicits are auto implicits.
Auto implicits are useful in a number of cases, typically where want to carray around information about properties of types.
For instance, in the ``base`` library, the definition of ``decEqInj : {auto 0 _ : Injective f} -> Dec (f x = f y) -> Dec (x = y)`` takes in the property that ``f`` is injective as part of a proof.
They are also how interfaces are implemented, where we ask the compiler to infer the instance given some context.

Regular implicits try to find a "necessary" match that is in scope.
 ``auto`` implicits, on the other hand, look for *any* possible construction of a value, even if it is not in scope, the compiler will attempt to construct a value for it.
This is useful for properties of types where we don't want to change the definition of the type but carry along some facts about it.


For instance, if we want to automatically pass a proof through some functions, we use ``auto`` implicits.

.. hint::
    Lowercase names in types are automatically universally quantified in types.
    For instance, ``map : (a -> b) -> List a -> List b`` is transformed into ``map : {0 a : Type} -> {0 b : Type} -> (a -> b) -> List a -> List b`` [#f1]_.
    You can write this signature explicitly, and it will compile the same as the simple version, and in addition you could also have the ``forall`` keyword and wrote this as ``map : forall a . forall b . ((a -> b) -> List a -> List b)``.

    If desired, this behavior can be toggled off by ``%unbound_implicits off`` (and back on by ``%unbound_implicits on``)



^^^^^^^^^^^^^
Quantities
^^^^^^^^^^^^^

Idris 2 uses Quantitative Type Theory (`QTT`_) as its theoretical basis.
In QTT, every variable has an associated multiplicity, ``0``, ``1``, or ω .
These correspond with how many times the given input is "used" in the result type.
``0`` corresponds to a value that is not used at runtime.
A value of ``1`` corresponds to a value being used exactly once, and ω (which, in Idris syntax is omitted) corresponds to a type having an unrestricted number of uses.

Note that there are some cases where a value of multiplictity of 0 appears to be being used.
For instance, in the linear library, there is the following function:

.. code-block:: idris

    mult : (1 n : LNat) -> (0 l : LNat) -> {auto 1 ls : toNat n `Copies` l} -> LNat

This appears to multiplity a value that is erased, but in fact, we never actually use the value of ``l``.
This is because the ``ls`` parameter allows us to create ``l`` copies of ``n`` at compile time, thereby avoiding the need to use ``l`` at runtime.

The syntax for specifying multiplicity in functions is ``(qty x : a) -> b`` (or any variation on such), where ``qty`` is the multiplicity either `0`, `1` or nothing for ω.
In addition, we may also declare ``let`` binding with a multiplicity, with the syntax ``let qty x : a = val in expr`` or ``let qty x = val in expr`` (an example of this is `toNat <https://www.idris-lang.org/Idris2/linear/docs/Data.Linear.LNat.html#Data.Linear.LNat.toNat>`_ ).

The syntax for specifying multiplicity in functions is ``(qty x : a) -> b`` (or any variation on such), where ``qty`` is the multiplicity either `0`, `1` or nothing for ω .
There is also a syntax for declaring top level definitions with a multiplictity, that being ``qty name : type``.


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
Inferable Placeholders
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

There is a class of expression that allow to call directly into Idris's inference machine, they are ``_``, ``?`` and ``?identifier``, where ``identifier`` is a valid variable name.

``_`` tells the compiler to wait for this expression to be resolved by another constraint, this is like a normal implicit argument.
``?`` tells the compiler to try to guess what the value is, this is like an auto-implicit.
``?identifiers`` is a **hole**. It allows you to query the type of the value at that point in the program.

.. caution::

    Holes are scoped over modules.

Named holes occur most often in the context of type inference.
Most often, this will occur in usages of generic types, where, for instance, given ``show : {a : Type} -> Show a => a -> String``, we transform the context ``show : {a : Type} -> Show a => a -> String, y = show x |- y : String`` to ``x : ?a, Show ?a |- y : String`` [#f2]_ .

``?`` acts as value that can be infererred.
Unlike named holes, however, it will either find a suitable value and *use* it, or fail, unlike named holes, which will never be filled in and will not fail.

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
