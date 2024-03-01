.. _builtins:

********
Builtins
********

.. role:: idris(code)
    :language: idris

Natural numbers
===============

Idris2 supports an optimized runtime representation of natural numbers (non-negative integers).
This optimization is automatic,
however it only works when natural numbers are represented in a specific way

Here is an example of a natural number that would be optimized:

.. code-block:: idris

    data Natural
        = Zero
        | Succ Natural

Natural numbers are generally represented as either zero or the successor (1 more than)
of another natural number. These are called Peano numbers.

At runtime, Idris2 will automatically represent this the same as the ``Integer`` type.
This will massively reduce the memory usage.

There are a few rules governing when this optimization occurs:

- The data type must have 2 constructors

  - After erasure of runtime irrelevant arguments
    + One must have no arguments
    + One must have exactly 1 argument (called ``Succ``)

- The type of the argument to ``Succ`` must have the same type constructor as the parent type.
  This means indexed data types, like ``Fin``, can be optimised.
- The argument to ``Succ`` must be strict, ie not ``Lazy Natural``

To ensure that a type is optimized to an ``Integer``, use ``%builtin Natural`` ie

.. code-block:: idris

    data MyNat
        = Succ MyNat
        | Zero

    %builtin Natural MyNat

Casting between natural numbers and integer
===========================================

Idris optimizes functions which convert between natural numbers and integers,
so that it takes constant time rather than linear time.

Such functions must be written in a specific way,
so that idris can detect that it can be optimised.

Here is an example of a natural to ``Integer`` function.

.. code-block:: idris

    cast : Natural -> Integer
    cast Z = 0
    cast (S k) = cast k + 1

This optimization is applied late in the compilation process,
so it may be sensitive to seemingly insignificant changes.

However here are roughly the rules governing this optimisation:

- Exactly one argument must be pattern matched on
  (any other forced or dotted patterns are allowed)
- The right hand side of the 'Zero' case must be ``0``
- The right hand side of the 'Succ' case must be ``1 + cast k``
  where ``k`` is the predecessor of the pattern matched argument

Casting from an ``Integer`` to a natural is a little more complex.

.. code-block:: idris

    castNonNegative : Integer -> Natural
    castNonNegative x = case x of
        0 => Zero
        _ => Succ $ castNonNegative (x - 1)

    cast : Integer -> Natural
    cast x = if x < 0 then Zero else castNonNegative x

For now you must manually check the given integer is non-negative.

If you are using an indexed data type it may be very hard to write
your ``Integer`` to natural cast in such a way,
so you can use ``%builtin IntegerToNatural`` to assert to the compiler
that a function is correct. It is your responsibility to make sure this is correct.

.. code-block:: idris

    module ComplexNat

    import Data.Maybe

    data ComplexNat
        = Zero
        | Succ ComplexNat

    integerToMaybeNat : Integer -> Maybe ComplexNat
    integerToMaybeNat _ = ...

    integerToNat :
        (x : Integer) ->
        {auto 0 prf : IsJust (ComplexNat.integerToMaybeNat x)} ->
        ComplexNat
    integerToNat x {prf} = fromJust (integerToMaybeNat x) @{prf}

    %builtin IntegerToNatural ComplexNat.integerToNat

Other operations
================

This can be used with ``%transform`` to allow many other operations to be O(1) too.

.. code-block:: idris

    eqNat : Nat -> Nat -> Bool
    eqNat Z Z = True
    eqNat (S j) (S k) = eqNat j k
    eqNat _ _ = False

    %transform "eqNat" eqNat j k = natToInteger j == natToInteger k

    plus : Nat -> Nat -> Nat
    plus Z y = y
    plus (S x) y = S $ plus x y

    %transform "plus" plus j k = integerToNat (natToInteger j + natToInteger j)

Compilation
===========

Here are the details of how natural numbers are compiled to ``Integer`` s.
Note: a numeric literal here is an ``Integer``.

``Zero`` => ``0``

``Succ k`` => ``1 + k``

.. code-block:: idris

    case k of
        Z => zexp
        S k' => sexp

=>

.. code-block:: idris

    case k of
        0 => zexp
        _ => let k' = k - 1 in sexp

