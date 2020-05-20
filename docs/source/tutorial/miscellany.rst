.. _sect-misc:

**********
Miscellany
**********

In this section we discuss a variety of additional features:

+ auto, implicit, and default arguments;
+ literate programming; and
+ the universe hierarchy.

Implicit arguments
==================

We have already seen implicit arguments, which allows arguments to be
omitted when they can be inferred by the type checker [#IdrisType]_, e.g.

.. code-block:: idris

    index : forall a, n . Fin n -> Vect n a -> a

Auto implicit arguments
-----------------------

In other situations, it may be possible to infer arguments not by type
checking but by searching the context for an appropriate value, or
constructing a proof. For example, the following definition of ``head``
which requires a proof that the list is non-empty:

.. code-block:: idris

    isCons : List a -> Bool
    isCons [] = False
    isCons (x :: xs) = True

    head : (xs : List a) -> (isCons xs = True) -> a
    head (x :: xs) _ = x

If the list is statically known to be non-empty, either because its
value is known or because a proof already exists in the context, the
proof can be constructed automatically. Auto implicit arguments allow
this to happen silently. We define ``head`` as follows:

.. code-block:: idris

    head : (xs : List a) -> {auto p : isCons xs = True} -> a
    head (x :: xs) = x

The ``auto`` annotation on the implicit argument means that Idris
will attempt to fill in the implicit argument by searching for a value
of the appropriate type. In fact, internally, this is exactly how interface
resolution works. It will try the following, in order:

- Local variables, i.e. names bound in pattern matches or ``let`` bindings,
  with exactly the right type.
- The constructors of the required type. If they have arguments, it will
  search recursively up to a maximum depth of 100.
- Local variables with function types, searching recursively for the
  arguments.
- Any function with the appropriate return type which is marked with the
  ``%hint`` annotation.

In the case that a proof is not found, it can be provided explicitly as normal:

.. code-block:: idris

    head xs {p = ?headProof}

Default implicit arguments
---------------------------

Besides having Idris automatically find a value of a given type, sometimes we
want to have an implicit argument with a specific default value. In Idris, we can
do this using the ``default`` annotation. While this is primarily intended to assist
in automatically constructing a proof where auto fails, or finds an unhelpful value,
it might be easier to first consider a simpler case, not involving proofs.

If we want to compute the n'th fibonacci number (and defining the 0th fibonacci
number as 0), we could write:

.. code-block:: idris

	fibonacci : {default 0 lag : Nat} -> {default 1 lead : Nat} -> (n : Nat) -> Nat
	fibonacci {lag} Z = lag
	fibonacci {lag} {lead} (S n) = fibonacci {lag=lead} {lead=lag+lead} n

After this definition, ``fibonacci 5`` is equivalent to ``fibonacci {lag=0} {lead=1} 5``,
and will return the 5th fibonacci number. Note that while this works, this is not the
intended use of the ``default`` annotation. It is included here for illustrative purposes
only. Usually, ``default`` is used to provide things like a custom proof search script.

Literate programming
====================

[NOT YET IN IDRIS 2]

Like Haskell, Idris supports *literate* programming. If a file has
an extension of ``.lidr`` then it is assumed to be a literate file. In
literate programs, everything is assumed to be a comment unless the line
begins with a greater than sign ``>``, for example:

.. code-block:: literate-idris
   :force:

    > module literate

    This is a comment. The main program is below

    > main : IO ()
    > main = putStrLn "Hello literate world!\n"

An additional restriction is that there must be a blank line between a
program line (beginning with ``>``) and a comment line (beginning with
any other character).

Cumulativity
============

[NOT YET IN IDRIS 2]

Since values can appear in types and *vice versa*, it is natural that
types themselves have types. For example:

::

    *universe> :t Nat
    Nat : Type
    *universe> :t Vect
    Vect : Nat -> Type -> Type

But what about the type of ``Type``? If we ask Idris it reports:

::

    *universe> :t Type
    Type : Type 1

If ``Type`` were its own type, it would lead to an inconsistency due to
`Girard’s paradox <http://www.cs.cmu.edu/afs/cs.cmu.edu/user/kw/www/scans/girard72thesis.pdf>`_,
so internally there is a *hierarchy* of types (or *universes*):

.. code-block:: idris

    Type : Type 1 : Type 2 : Type 3 : ...

Universes are *cumulative*, that is, if ``x : Type n`` we can also have
that ``x : Type m``, as long as ``n < m``. The typechecker generates
such universe constraints and reports an error if any inconsistencies
are found. Ordinarily, a programmer does not need to worry about this,
but it does prevent (contrived) programs such as the following:

.. code-block:: idris

    myid : (a : Type) -> a -> a
    myid _ x = x

    idid :  (a : Type) -> a -> a
    idid = myid _ myid

The application of ``myid`` to itself leads to a cycle in the universe
hierarchy — ``myid``\ ’s first argument is a ``Type``, which cannot be
at a lower level than required if it is applied to itself.

.. [#IdrisType] https://github.com/david-christiansen/idris-type-providers
