Before we discuss the details of theorem proving in Idris, we will describe
some fundamental concepts:

-  Propositions and judgments
-  Boolean and constructive logic
-  Curry-Howard correspondence
-  Definitional and propositional equalities
-  Axiomatic and constructive approaches

Propositions and Judgments
==========================

Propositions are the subject of our proofs. Before the proof, we can't
formally say if they are true or not. If the proof is successful then the
result is a 'judgment'.  For instance, if the ``proposition`` is,

+-------+
| 1+1=2 |
+-------+

When we prove it, the ``judgment`` is,

+------------+
| 1+1=2 true |
+------------+

Or if the ``proposition`` is,

+-------+
| 1+1=3 |
+-------+

we can't prove it is true, but it is still a valid proposition and perhaps we
can prove it is false so the ``judgment`` is, 

+-------------+
| 1+1=3 false |
+-------------+

This may seem a bit pedantic but it is important to be careful: in mathematics
not every proposition is true or false. For instance, a proposition may be
unproven or even unprovable.

So the logic here is different from the logic that comes from boolean algebra.
In that case what is not true is false and what is not false is true. The logic
we are using here does not have this law, the "Law of Excluded Middle", so we
cannot use it.

A false proposition is taken to be a contradiction and if we have a
contradiction then we can prove anything, so we need to avoid this. Some
languages, used in proof assistants, prevent contradictions.

The logic we are using is called constructive (or sometimes intuitional)
because we are constructing a 'database' of judgments.

Curry-Howard correspondence
---------------------------

So how do we relate these proofs to Idris programs? It turns out that there is
a correspondence between constructive logic and type theory. They have the same
structure and we can switch back and forth between the two notations.

The way that this works is that a proposition is a type so...

.. code-block:: idris

    Main> 1 + 1 = 2
    2 = 2

    Main> :t 1 + 1 = 2
    (fromInteger 1 + fromInteger 1) === fromInteger 2 : Type

...is a proposition and it is also a type. The
following will also produce an equality type:


.. code-block:: idris

   Main> 1 + 1 = 3
   2 = 3

Both of these are valid propositions so both are valid equality types. But how
do we represent a true judgment? That is, how do we denote 1+1=2 is true but not
1+1=3?  A type that is true is inhabited, that is, it can be constructed. An
equality type has only one constructor 'Refl' so a proof of 1+1=2 is

.. code-block:: idris

   onePlusOne : 1+1=2
   onePlusOne = Refl

Now that we can represent propositions as types other aspects of
propositional logic can also be translated to types as follows:

+----------+-------------------+--------------------------+
|          | propositions      | example of possible type |
+----------+-------------------+--------------------------+
| A        | x=y               |                          |
+----------+-------------------+--------------------------+
| B        | y=z               |                          |
+----------+-------------------+--------------------------+
| and      | A /\ B            | Pair(x=y,y=z)            |
+----------+-------------------+--------------------------+
| or       | A \/ B            | Either(x=y,y=z)          |
+----------+-------------------+--------------------------+
| implies  | A -> B            | (x=y) -> (y=x)           |
+----------+-------------------+--------------------------+
| for all  | y=z               |                          |
+----------+-------------------+--------------------------+
| exists   | y=z               |                          |
+----------+-------------------+--------------------------+


And (conjunction)
-----------------

We can have a type which corresponds to conjunction:

.. code-block:: idris

   AndIntro : a -> b -> A a b

There is a built in type called 'Pair'.

Or (disjunction)
----------------

We can have a type which corresponds to disjunction:

.. code-block:: idris

   data Or : Type -> Type -> Type where
   OrIntroLeft : a -> A a b
   OrIntroRight : b -> A a b

There is a built in type called 'Either'.

Definitional and Propositional Equalities
-----------------------------------------

We have seen that  we can 'prove' a type by finding a way to construct a term.
In the case of equality types there is only one constructor which is ``Refl``.
We have also seen that each side of the equation does not have to be identical
like '2=2'. It is enough that both sides are *definitionally equal* like this:

.. code-block:: idris

   onePlusOne : 1+1=2
   onePlusOne = Refl

Both sides of this equation normalise to 2 and so Refl matches and the
proposition is proved.

We don't have to stick to terms; we can also use symbolic parameters so the
following type checks:

.. code-block:: idris

   varIdentity : m = m
   varIdentity = Refl

If a proposition/equality type is not definitionally equal but is still true
then it is *propositionally equal*. In this case we may still be able to prove
it but some steps in the proof may require us to add something into the terms
or at least to take some sideways steps to get to a proof.

Especially when working with equalities containing variable terms (inside
functions) it can be hard to know which equality types are definitionally equal,
in this example ``plusReducesL`` is *definitionally equal* but ``plusReducesR`` is
not (although it is *propositionally equal*). The only difference between
them is the order of the operands.

.. code-block:: idris

   plusReducesL : (n:Nat) -> plus Z n = n
   plusReducesL n = Refl

   plusReducesR : (n:Nat) -> plus n Z = n
   plusReducesR n = Refl

Checking ``plusReducesR`` gives the following error:


.. code-block:: idris

    Proofs.idr:21:18--23:1:While processing right hand side of Main.plusReducesR at Proofs.idr:21:1--23:1:
    Can't solve constraint between:
            plus n Z
    and
            n

So why is ``Refl`` able to prove some equality types but not others?

The first answer is that ``plus`` is defined by recursion on its first
argument. So, when the first argument is ``Z``, it reduces, but not when the
second argument is ``Z``.

If an equality type can be proved/constructed by using ``Refl`` alone it is known
as a *definitional equality*. In order to be definitionally equal both sides
of the equation must normalise to the same value.

So when we type ``1+1`` in Idris it is immediately reduced to 2 because
definitional equality is built in

.. code-block:: idris

    Main> 1+1
    2

In the following pages we discuss how to resolve propositional equalities.
