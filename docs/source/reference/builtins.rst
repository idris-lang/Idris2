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