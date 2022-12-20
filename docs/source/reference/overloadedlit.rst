Overloaded literals
===================

.. role:: idris(code)
    :language: idris

The compiler provides directives for literals overloading, respectively
``%stringLit <fun>`` and ``%integerLit <fun>`` for string and integer literals. During
elaboration, the given function is applied to the corresponding literal.
In the Prelude these functions are set to ``fromString`` and ``fromInteger``.

The interface ``FromString ty`` provides the ``fromString : String -> ty`` function,
while the ``Num ty`` interface provides the ``fromInteger : Integer -> ty`` function
for all numerical types.

Restricted overloads
--------------------
Although the overloading of literals can be achieved by implementing the interfaces
described above, in principle only a function with the correct signature and name
is enough to achieve the desired behaviour. This can be exploited to obtain more
restrictive overloading such as converting literals to ``Fin n`` values, where
integer literals greater or equal to n are not constructible values for the type.
Additional implicit arguments can be added to the function signature, in particular
auto implicit arguments for searching proofs. As an example, this is the implementation
of ``fromInteger`` for ``Fin n``.

.. code-block:: idris

    public export
    fromInteger : (x : Integer) -> {n : Nat} ->
                  {auto prf : (IsJust (integerToFin x n))} ->
                  Fin n
    fromInteger {n} x {prf} with (integerToFin x n)
      fromInteger {n} x {prf = ItIsJust} | Just y = y

The ``prf`` auto implicit is an automatically constructed proof (if possible) that
the literal is suitable for the ``Fin n`` type. The restricted behaviour can be
observed in the REPL, where the failure to construct a valid proof is caught during
the type-checking phase and not at runtime:

.. code-block:: idris

    Main> the (Fin 3) 2
    FS (FS FZ)
    Main> the (Fin 3) 5
    (interactive):1:13--1:14:Can't find an implementation for IsJust (integerToFin 5 3) at:
    1	the (Fin 3) 5
