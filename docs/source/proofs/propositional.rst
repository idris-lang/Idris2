This page attempts to explain some of the techniques used in Idris to prove
propositional equalities.

Proving Propositional Equality
==============================

We have seen that definitional equalities can be proved using ``Refl`` since they
always normalise to values that can be compared directly.

However with propositional equalities we are using symbolic variables, which do
not always normalse.

So to take the previous example:

.. code-block:: idris

    plusReducesR : (n : Nat) -> plus n Z = n

In this case ``plus n Z`` does not normalise to n. Even though both sides of
the equality are provably equal we cannot claim ``Refl`` as a proof.

If the pattern match cannot match for all ``n`` then we need to
match all possible values of ``n``. In this case

.. code-block:: idris

   plusReducesR : (n : Nat) -> plus n Z = n
   plusReducesR Z = Refl
   plusReducesR (S k) 
       = let rec = plusReducesR k in
             rewrite sym rec in Refl

we can't use ``Refl`` to prove ``n = plus n 0`` for all ``n``. Instead, we call
it for each case separately.  So, in the second line for example, the type checker
substitutes ``Z`` for ``n`` in the type being matched, and reduces the type
accordingly.

Replace
=======

This implements the 'indiscernability of identicals' principle, if two terms
are equal then they have the same properties. In other words, if ``x=y``, then we
can substitute y for x in any expression. In our proofs we can express this as:

   if x=y
   then prop x = prop y

where prop is a pure function representing the property. In the examples below
prop is an expression in some variable with a type like this: ``prop: n -> Type``

So if ``n`` is a natural number variable then ``prop`` could be something
like ``\n => 2*n + 3``.

To use this in our proofs there is the following function in the prelude:

.. code-block:: idris

   ||| Perform substitution in a term according to some equality.
   replace : forall x, y, prop . (0 rule : x = y) -> prop x -> prop y
   replace Refl prf = prf

If we supply an equality (x=y) and a proof of a property of x (``prop x``) then we get
a proof of a property of y (``prop y``).
So, in the following example, if we supply ``p1 x`` which is a proof that ``x=2`` and
the equality ``x=y`` then we get a proof that ``y=2``.

.. code-block:: idris

   p1: Nat -> Type
   p1 n = (n=2)

   testReplace: (x=y) -> (p1 x) -> (p1 y)
   testReplace a b = replace a b

Rewrite
=======

In practice, ``replace`` can be
a little tricky to use because in general the implicit argument ``prop``
can be hard to infer for the machine, so Idris provides a high level
syntax which calculates the property and applies ``replace``.

Example: again we supply ``p1`` which is a proof that ``x=2`` and the equality
``x=y`` then we get a proof that ``y=2``.

.. code-block:: idris

   p1: Nat -> Type
   p1 x = (x=2)

   testRewrite2: (x=y) -> (p1 y) -> (p1 x)
   testRewrite2 a b = rewrite a in b

We can think of ``rewrite`` as working in this way:

 * Start with a equation ``x=y`` and a property ``prop : x -> Type``
 * Search for ``x`` in ``prop``
 * Replaces all occurrences of ``x`` with ``y`` in ``prop``.

That is, we are doing a substitution.

Symmetry and Transitivity
=========================

In addition to 'reflexivity' equality also obeys 'symmetry' and 'transitivity'
and these are also included in the prelude:

.. code-block:: idris

   ||| Symmetry of propositional equality
   sym : forall x, y . (0 rule : x = y) -> y = x
   sym Refl = Refl

   ||| Transitivity of propositional equality
   trans : forall a, b, c . (0 l : a = b) -> (0 r : b = c) -> a = c
   trans Refl Refl = Refl

Heterogeneous Equality
======================

Also included in the prelude: 

.. code-block:: idris

   ||| Explicit heterogeneous ("John Major") equality. Use this when Idris
   ||| incorrectly chooses homogeneous equality for `(=)`.
   ||| @ a the type of the left side
   ||| @ b the type of the right side
   ||| @ x the left side
   ||| @ y the right side
   (~=~) : (x : a) -> (y : b) -> Type
   (~=~) x y = (x = y)



