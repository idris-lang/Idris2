***********************
Pattern Matching Proofs
***********************

In this section, we will provide a proof of ``plus_commutes`` directly,
by writing a pattern matching definition. We will use interactive
editing features extensively, since it is significantly easier to
produce a proof when the machine can give the types of intermediate
values and construct components of the proof itself. The commands we
will use are summarised below. Where we refer to commands
directly, we will use the Vim version, but these commands have a direct
mapping to Emacs commands.

+---------------------+-----------------+---------------+--------------------------------------------------------------------------------------------+
|Command              | Vim binding     | Emacs binding | Explanation                                                                                |
+---------------------+-----------------+---------------+--------------------------------------------------------------------------------------------+
| Check type          | ``\t``          | ``C-c C-t``   | Show type of identifier or hole under the cursor.                                          |
+---------------------+-----------------+---------------+--------------------------------------------------------------------------------------------+
| Proof search        | ``\s``          | ``C-c C-a``   | Attempt to solve hole under the cursor by applying simple proof search.                    |
+---------------------+-----------------+---------------+--------------------------------------------------------------------------------------------+
| Make new definition | ``\a``          | ``C-c C-s``   | Add a template definition for the type defined under the cursor.                           |
+---------------------+-----------------+---------------+--------------------------------------------------------------------------------------------+
| Make lemma          | ``\l``          | ``C-c C-e``   | Add a top level function with a type which solves the hole under the cursor.               |
+---------------------+-----------------+---------------+--------------------------------------------------------------------------------------------+
| Split cases         | ``\c``          | ``C-c C-c``   | Create new constructor patterns for each possible case of the variable under the cursor.   |
+---------------------+-----------------+---------------+--------------------------------------------------------------------------------------------+


Creating a Definition
=====================

To begin, create a file ``pluscomm.idr`` containing the following type
declaration:

.. code-block:: idris

    plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n

To create a template definition for the proof, press ``\a`` (or the
equivalent in your editor of choice) on the line with the type
declaration. You should see:

.. code-block:: idris

    plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
    plus_commutes n m = ?plus_commutes_rhs

To prove this by induction on ``n``, as we sketched in Section
:ref:`sect-inductive`, we begin with a case split on ``n`` (press
``\c`` with the cursor over the ``n`` in the definition.) You
should see:

.. code-block:: idris

    plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
    plus_commutes Z m = ?plus_commutes_rhs_1
    plus_commutes (S k) m = ?plus_commutes_rhs_2

If we inspect the types of the newly created holes,
``plus_commutes_rhs_1`` and ``plus_commutes_rhs_2``, we see that the
type of each reflects that ``n`` has been refined to ``Z`` and ``S k``
in each respective case. Pressing ``\t`` over
``plus_commutes_rhs_1`` shows:

.. code-block:: idris

       m : Nat
    -------------------------------------
    plus_commutes_rhs_1 : m = plus m Z

Similarly, for ``plus_commutes_rhs_2``:

.. code-block:: idris

      k : Nat
      m : Nat
    --------------------------------------
    plus_commutes_rhs_2 : (S (plus k m)) = (plus m (S k))

It is a good idea to give these slightly more meaningful names:

.. code-block:: idris

    plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
    plus_commutes Z m = ?plus_commutes_Z
    plus_commutes (S k) m = ?plus_commutes_S

Base Case
=========

We can create a separate lemma for the base case interactively, by
pressing ``\l`` with the cursor over ``plus_commutes_Z``. This
yields:

.. code-block:: idris

    plus_commutes_Z : (m : Nat) -> m = plus m Z

    plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
    plus_commutes Z m = plus_commutes_Z m
    plus_commutes (S k) m = ?plus_commutes_S

That is, the hole has been filled with a call to a top level
function ``plus_commutes_Z``, applied to the variable in scope ``m``. 

Unfortunately, we cannot prove this lemma directly, since ``plus`` is
defined by matching on its *first* argument, and here ``plus m Z`` has a
concrete value for its *second argument* (in fact, the left hand side of
the equality has been reduced from ``plus Z m``.) Again, we can prove
this by induction, this time on ``m``.

First, create a template definition with ``\d``:

.. code-block:: idris

    plus_commutes_Z : (m : Nat) -> m = plus m Z 
    plus_commutes_Z m = ?plus_commutes_Z_rhs

Now, case split on ``m`` with ``\c``:

.. code-block:: idris

    plus_commutes_Z : (m : Nat) -> m = plus m Z 
    plus_commutes_Z Z = ?plus_commutes_Z_rhs_1
    plus_commutes_Z (S k) = ?plus_commutes_Z_rhs_2

Checking the type of ``plus_commutes_Z_rhs_1`` shows the following,
which is provable by ``Refl``:

.. code-block:: idris

    --------------------------------------
    plus_commutes_Z_rhs_1 : Z = Z

For such immediate proofs, we can let write the proof automatically by
pressing ``\s`` with the cursor over ``plus_commutes_Z_rhs_1``.
This yields:

.. code-block:: idris

    plus_commutes_Z : (m : Nat) -> m = plus m Z
    plus_commutes_Z Z = Refl
    plus_commutes_Z (S k) = ?plus_commutes_Z_rhs_2

For ``plus_commutes_Z_rhs_2``, we are not so lucky:

.. code-block:: idris

       k : Nat
    -------------------------------------
    plus_commutes_Z_rhs_2 : S k = S (plus k Z)

Inductively, we should know that ``k = plus k Z``, and we can get access
to this inductive hypothesis by making a recursive call on k, as
follows:

.. code-block:: idris

    plus_commutes_Z : (m : Nat) -> m = plus m Z
    plus_commutes_Z Z = Refl
    plus_commutes_Z (S k)
       = let rec = plus_commutes_Z k in
             ?plus_commutes_Z_rhs_2

For ``plus_commutes_Z_rhs_2``, we now see:

.. code-block:: idris

       k : Nat
       rec : k = plus k Z
    -------------------------------------
    plus_commutes_Z_rhs_2 : S k = S (plus k Z)

So we know that ``k = plus k Z``, but how do we use this to update the goal to
``S k = S k``?

To achieve this, Idris provides a ``replace`` function as part of the
prelude:

.. code-block:: idris

    Main> :t replace
    Builtin.replace : (0 rule : x = y) -> p x -> p y

Given a proof that ``x = y``, and a property ``p`` which holds for
``x``, we can get a proof of the same property for ``y``, because we
know ``x`` and ``y`` must be the same. Note the multiplicity on ``rule``
means that it's guaranteed to be erased at run time.
In practice, this function can be
a little tricky to use because in general the implicit argument ``p``
can be hard to infer by unification, so Idris provides a high level
syntax which calculates the property and applies ``replace``:

.. code-block:: idris

    rewrite prf in expr

If we have ``prf : x = y``, and the required type for ``expr`` is some
property of ``x``, the ``rewrite ... in`` syntax will search for all
occurrences of ``x``
in the required type of ``expr`` and replace them with ``y``. We want
to replace ``plus k Z`` with ``k``, so we need to apply our rule
``rec`` in reverse, which we can do using ``sym`` from the Prelude

.. code-block:: idris

    Main> :t sym
    Builtin.sym : (0 rule : x = y) -> y = x

Concretely, in our example, we can say:

.. code-block:: idris

    plus_commutes_Z (S k)
       = let rec = plus_commutes_Z k in
             rewrite sym rec in ?plus_commutes_Z_rhs_2

Checking the type of ``plus_commutes_Z_rhs_2`` now gives:

.. code-block:: idris

       k : Nat
       rec : k = plus k Z
    -------------------------------------
    plus_commutes_Z_rhs_2 : S k = S k

Using the rewrite rule ``rec``, the goal type has been updated with ``plus k Z``
replaced by ``k``.

We can use proof search (``\s``) to complete the proof, giving:

.. code-block:: idris

    plus_commutes_Z : (m : Nat) -> m = plus m Z
    plus_commutes_Z Z = Refl
    plus_commutes_Z (S k)
       = let rec = plus_commutes_Z k in
             rewrite sym rec in Refl

The base case of ``plus_commutes`` is now complete.

Inductive Step
==============

Our main theorem, ``plus_commutes`` should currently be in the following
state:

.. code-block:: idris

    plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
    plus_commutes Z m = plus_commutes_Z m
    plus_commutes (S k) m = ?plus_commutes_S

Looking again at the type of ``plus_commutes_S``, we have:

.. code-block:: idris

       k : Nat
       m : Nat
    -------------------------------------
    plus_commutes_S : S (plus k m) = plus m (S k)

Conveniently, by induction we can immediately tell that
``plus k m = plus m k``, so let us rewrite directly by making a
recursive call to ``plus_commutes``. We add this directly, by hand, as
follows:

.. code-block:: idris

    plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
    plus_commutes Z m = plus_commutes_Z
    plus_commutes (S k) m = rewrite plus_commutes k m in ?plus_commutes_S

Checking the type of ``plus_commutes_S`` now gives:

.. code-block:: idris

       k : Nat
       m : Nat
    -------------------------------------
    plus_commutes_S : S (plus m k) = plus m (S k)

The good news is that ``m`` and ``k`` now appear in the correct order.
However, we still have to show that the successor symbol ``S`` can be
moved to the front in the right hand side of this equality. This
remaining lemma takes a similar form to the ``plus_commutes_Z``; we
begin by making a new top level lemma with ``\l``. This gives:

.. code-block:: idris

    plus_commutes_S : (k : Nat) -> (m : Nat) -> S (plus m k) = plus m (S k)

Again, we make a template definition with ``\a``:

.. code-block:: idris

    plus_commutes_S : (k : Nat) -> (m : Nat) -> S (plus m k) = plus m (S k)
    plus_commutes_S k m = ?plus_commutes_S_rhs

Like ``plus_commutes_Z``, we can define this by induction over ``m``, since
``plus`` is defined by matching on its first argument. The complete definition
is:

.. code-block:: idris

    total
    plus_commutes_S : (k : Nat) -> (m : Nat) -> S (plus m k) = plus m (S k)
    plus_commutes_S k Z = Refl
    plus_commutes_S k (S j) = rewrite plus_commutes_S k j in Refl

All holes have now been solved.

The ``total`` annotation means that we require the final function to
pass the totality checker; i.e. it will terminate on all possible
well-typed inputs. This is important for proofs, since it provides a
guarantee that the proof is valid in *all* cases, not just those for
which it happens to be well-defined.

Now that ``plus_commutes`` has a ``total`` annotation, we have completed the
proof of commutativity of addition on natural numbers.
