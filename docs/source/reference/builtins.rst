.. _builtins:

********
Builtins
********

.. role:: idris(code)
    :language: idris

Idris2 supports an optimised runtime representation of some types,
using the ``%builtin`` pragma.
For now only ``Nat``-like types has been implemented.

``%builtin Natural``
====================

I suggest having a look at the source for ``Nat`` (in ``Prelude.Types``) before reading this section.

The ``%builtin Natural`` pragma converts recursive/unary representations of natural numbers
into primitive ``Integer`` representations.
This massively reduces the memory usage and offers a small speed improvement,
for example with the unary representation ``the Nat 1000`` would take up about 2000 * 8 bytes
(1000 for the tag, 1000 for the pointers) whereas the ``Integer`` representation takes about 8 to 16 bytes.

Here's an example:

.. code-block:: idris

    data Nat
        = Z
        | S Nat

    %builtin Natural Nat

Note that the order of the constructors doesn't matter.
Furthermore this pragma supports GADTs
so long as any extra arguments are erased.

For example:

.. code-block:: idris

    data Fin : Nat -> Type where
        FZ : Fin (S k)
        FS : Fin k -> Fin (S k)

    %builtin Natural Fin

works because the ``k`` is always erased.

This doesn't work if the argument to the ``S``-like constructor
is ``Inf`` (sometime known as ``CoNat``) as these can be infinite
or is ``Lazy`` as it wouldn't preserve laziness semantics.

During codegen any occurance of ``Nat`` will be converted to the faster ``Integer`` implementation.
Here are the specifics for the conversion:

``Z`` => ``0``

``S k`` => ``1 + k``

.. code-block:: idris

    case k of
        Z => zexp
        S k' => sexp

=>

.. code-block:: idris

    case k of
        0 => zexp
        _ => let k' = k - 1 in sexp

``%builtin NaturalToInteger``
=============================

The ``%builtin NaturalToInteger`` pragma allows O(1) conversion of naturals to ``Integer`` s.
For example

.. code-block:: idris

    natToInteger : Nat -> Integer
    natToInteger Z = 0
    natToInteger (S k) = 1 + natToInteger k

    %builtin NaturalToInteger natToInteger

For now, any ``NaturalToInteger`` function must have exactly 1 non-erased argument, which must be a natural.

``%builtin IntegerToNatural``
=============================

The ``%builtin IntegerToNatural`` pragma allows O(1) conversion of ``Integer`` s to naturals.
For example

.. code-block:: idris

    integerToNat : Integer -> Nat
    integerToNat x = if x <= 0
        then Z
        else S $ integerToNat (x - 1)

Any ``IntegerToNatural`` function must have exactly 1 unrestricted ``Integer`` argument and the return type must be a natural.

Please note, ``NaturalToInteger`` and ``IntegerToNatural`` only check the type, not that the function is correct.

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
