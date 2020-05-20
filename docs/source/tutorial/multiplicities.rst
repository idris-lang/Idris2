.. _sect-multiplicities:

**************
Multiplicities
**************

Idris 2 is
based on `Quantitative Type Theory (QTT)
<https://bentnib.org/quantitative-type-theory.html>`_, a core language
developed by Bob Atkey and Conor McBride. In practice, this means that every
variable in Idris 2 has a *quantity* associated with it. A quantity is one of:

* ``0``, meaning that the variable is *erased* at run time
* ``1``, meaning that the variable is used *exactly once* at run time
* *Unrestricted*, which is the same behaviour as Idris 1

We can see the multiplicities of variables by inspecting holes. For example,
if we have the following skeleton definition of ``append`` on vectors...

.. code-block:: idris

    append : Vect n a -> Vect m a -> Vect (n + m) a
    append xs ys = ?append_rhs

...we can look at the hole ``append_rhs``:

::

    Main> :t append_rhs
     0 m : Nat
     0 a : Type
     0 n : Nat
       ys : Vect m a
       xs : Vect n a
    -------------------------------------
    append_rhs : Vect (plus n m) a

The ``0`` next to ``m``, ``a`` and ``n`` mean that they are in scope, but there
will be ``0`` occurrences at run-time. That is, it is **guaranteed** that they
will be erased at run-time.

Multiplicities can be explicitly written in function types as follows:

* ``ignoreN : (0 n : Nat) -> Vect n a -> Nat`` - this function cannot look at
  ``n`` at run time
* ``duplicate : (1 x : a) -> (a, a)`` - this function must use ``x`` exactly
  once (so good luck implementing it, by the way. There is no implementation
  because it would need to use ``x`` twice!)

If there is no multiplicity annotation, the argument is unrestricted.
If, on the other hand, a name is implicitly bound (like ``a`` in both examples above)
the argument is erased. So, the above types could also be written as:

* ``ignoreN : {0 a : _} -> (0 n : Nat) -> Vect n a -> Nat``
* ``duplicate : {0 a : _} -> (1 x : a) -> (a, a)``

This section describes what this means for your Idris 2 programs in practice,
with several examples. In particular, it describes:

* :ref:`sect-erasure` - how to know what is relevant at run time and what is erased
* :ref:`sect-linearity` - using the type system to encode *resource usage protocols*
* :ref:`sect-pmtypes` - truly first class types

The most important of these for most programs, and the thing you'll need to
know about if converting Idris 1 programs to work with Idris 2, is erasure_.
The most interesting, however, and the thing which gives Idris 2 much more
expressivity, is linearity_, so we'll start there.

.. _sect-linearity:

Linearity
---------

The ``1`` multiplicity expresses that a variable must be used exactly once.
First, we'll see how this works on some small examples of functions and
data types, then see how it can be used to encode `resource protocols`_.

Above, we saw the type of ``duplicate``. Let's try to write it interactively,
and see what goes wrong. We'll start by giving the type and a skeleton
definition with a hole

.. code-block:: idris

    duplicate : (1 x : a) -> (a, a)
    duplicate x = ?help

Checking the type of a hole tells us the multiplicity of each variable in
scope. If we check the type of ``?help`` we'll see that we can't
use ``a`` at run time, and we have to use ``x`` exactly once::

  Main> :t help
   0 a : Type
   1 x : a
  -------------------------------------
  help : (a, a)

If we use ``x`` for one part of the pair...

.. code-block:: idris

    duplicate : (1 x : a) -> (a, a)
    duplicate x = (x, ?help)

...then the type of the remaining hole tells us we can't use it for the other::

  Main> :t help
   0 a : Type
   0 x : a
  -------------------------------------
  help : a

The same happens if we try defining ``duplicate x = (?help, x)`` (try it!)
The intution behind multiplicity ``1`` is that if we have a function with
a type of the following form...

.. code-block:: idris

    f : (1 x : a) -> b

...then the guarantee given by the type system is that *if* ``f x`` *is used
exactly once, then* ``x`` *is used exactly once*. So, if we insist on
trying to define ``duplicate``...::

  duplicate x = (x, x)

...then Idris will complain::

  pmtype.idr:2:15--8:1:While processing right hand side of Main.duplicate at pmtype.idr:2:1--8:1:
  There are 2 uses of linear name x

A similar intuition applies for data types. Consider the following types,
``Lin`` which wraps an argument that must be used once, and ``Unr`` which
wraps an argument with unrestricted use

.. code-block:: idris

    data Lin : Type -> Type where
         MkLin : (1 x : a) -> Lin a
  
    data Unr : Type -> Type where
         MkUnr : (x : a) -> Unr a
  
If ``MkLin x`` is used once, then ``x`` is used once. But if ``MkUnr x`` is
used once, there is no guarantee on how often ``x`` is used. We can see this a
bit more clearly by starting to write projection functions for ``Lin`` and
``Unr`` to extract the argument

.. code-block:: idris

    getLin : (1 val : Lin a) -> a
    getLin (MkLin x) = ?howmanyLin
  
    getUnr : (1 val : Unr a) -> a
    getUnr (MkUnr x) = ?howmanyUnr
  
Checking the types of the holes shows us that, for ``getLin``, we must use
``x`` exactly once (Because the ``val`` argument is used once,
by pattern matching on it as ``MkLin x``, and if ``MkLin x`` is used once,
``x`` must be used once)::

  Main> :t howmanyLin
   0 a : Type
   1 x : a
  -------------------------------------
  howmanyLin : a

For ``getUnr``, however, we still have to use ``val`` once, again by pattern
matching on it, but using ``MkUnr x`` once doesn't place any restrictions on
``x``. So, ``x`` has unrestricted use in the body of ``getUnr``::

  Main> :t howmanyUnr
   0 a : Type
     x : a
  -------------------------------------
  howmanyUnr : a

If ``getLin`` has an unrestricted argument...

.. code-block:: idris

    getLin : (val : Lin a) -> a
    getLin (MkLin x) = ?howmanyLin

...then ``x`` is unrestricted in ``howmanyLin``::
  
  Main> :t howmanyLin
   0 a : Type
     x : a
  -------------------------------------
  howmanyLin : a

Remember the intuition from the type of ``MkLin`` is that if ``MkLin x`` is
used exactly once, ``x`` is used exactly once. But, we didn't say that
``MkLin x`` would be used exactly once, so there is no restriction on ``x``.

Resource protocols
~~~~~~~~~~~~~~~~~~

One way to take advantage of being able to express linear usage of an argument
is in defining resource usage protocols, where we can use linearity to ensure
that any unique external resource has only one instance, and we can use
functions which are linear in their arguments to represent state transitions on
that resource. A door, for example, can be in one of two states, ``Open`` or
``Closed``

.. code-block:: idris

    data DoorState = Open | Closed

    data Door : DoorState -> Type where
         MkDoor : (doorId : Int) -> Door st

(Okay, we're just pretending here - imagine the ``doorId`` is a reference
to an external resource!)

We can define functions for opening and closing the door which explicitly
describe how they change the state of a door, and that they are linear in
the door

.. code-block:: idris

    openDoor : (1 d : Door Closed) -> Door Open
    closeDoor : (1 d : Door Open) -> Door Closed

Remember, the intuition is that if ``openDoor d`` is used exactly once,
then ``d`` is used exactly once. So, provided that a door ``d`` has
multiplicity ``1`` when it's created, we *know* that once we call
``openDoor`` on it, we won't be able to use ``d`` again. Given that
``d`` is an external resource, and ``openDoor`` has changed it's state,
this is a good thing!

We can ensure that any door we create has multiplicity ``1`` by
creating them with a ``newDoor`` function with the following type

.. code-block:: idris

    newDoor : (1 p : (1 d : Door Closed) -> IO ()) -> IO ()

That is, ``newDoor`` takes a function, which it runs exactly once. That
function takes a door, which is used exactly once. We'll run it in
``IO`` to suggest that there is some interaction with the outside world
going on when we create the door. Since the multiplicity ``1`` means the
door has to be used exactly once, we need to be able to delete the door
when we're finished

.. code-block:: idris

    deleteDoor : (1 d : Door Closed) -> IO ()

So an example correct door protocol usage would be

.. code-block:: idris

    doorProg : IO ()
    doorProg 
        = newDoor $ \d =>
              let d' = openDoor d
                  d'' = closeDoor d' in
                  deleteDoor d''
 
It's instructive to build this program interactively, with holes along
the way, and see how the multiplicities of ``d``, ``d'`` etc change. For
example

.. code-block:: idris

    doorProg : IO ()
    doorProg 
        = newDoor $ \d =>
              let d' = openDoor d in
                  ?whatnow

Checking the type of ``?whatnow`` shows that ``d`` is now spent, but we
still have to use ``d'`` exactly once::

  Main> :t whatnow
   0 d : Door Closed
   1 d' : Door Open
  -------------------------------------
  whatnow : IO ()

Note that the ``0`` multiplicity for ``d`` means that we can still *talk*
about it - in particular, we can still reason about it in types - but we
can't use it again in a relevant position in the rest of the program.
It's also fine to shadow the name ``d`` throughout

.. code-block:: idris

    doorProg : IO ()
    doorProg 
        = newDoor $ \d =>
              let d = openDoor d
                  d = closeDoor d in
                  deleteDoor d

If we don't follow the protocol correctly - create the door, open it, close
it, then delete it - then the program won't type check. For example, we
can try not to delete the door before finishing

.. code-block:: idris

    doorProg : IO ()
    doorProg 
        = newDoor $ \d =>
              let d' = openDoor d
                  d'' = closeDoor d' in
                  putStrLn "What could possibly go wrong?"

This gives the following error::

  Door.idr:15:19--15:38:While processing right hand side of Main.doorProg at Door.idr:13:1--17:1:
  There are 0 uses of linear name d''

There's a lot more to be said about the details here! But, this shows at
a high level how we can use linearity to capture resource usage protocols
at the type level. If we have an external resource which is guaranteed to
be used linearly, like ``Door``, we don't need to run operations on that
resource in an ``IO`` monad, since we're already enforcing an ordering on
operations and don't have access to any out of date resource states. This is
similar to the way interactive programs work in 
`the Clean programming language <https://clean.cs.ru.nl/Clean>`_, and in
fact is how ``IO`` is implemented internally in Idris 2, with a special
``%World`` type for representing the state of the outside world that is
always used linearly

.. code-block:: idris

    public export
    data IORes : Type -> Type where
         MkIORes : (result : a) -> (1 x : %World) -> IORes a

    export
    data IO : Type -> Type where
         MkIO : (1 fn : (1 x : %World) -> IORes a) -> IO a

Having multiplicities in the type system raises several interesting
questions, such as:

* Can we use linearity information to inform memory management and, for
  example, have type level guarantees about functions which will not need
  to perform garbage collection?
* How should multiplicities be incorporated into interfaces such as
  ``Functor``, ``Applicative`` and ``Monad``?
* If we have ``0``, and ``1`` as multiplicities, why stop there? Why not have
  ``2``, ``3`` and more (like `Granule
  <https://granule-project.github.io/granule.html>`_)
* What about multiplicity polymorphism, as in the `Linear Haskell proposal <https://arxiv.org/abs/1710.09756>`_?
* Even without all of that, what can we do *now*?

.. _sect-erasure:

Erasure
-------

The ``1`` multiplicity give us many possibilities in the kinds of
properties we can express. But, the ``0`` multiplicity is perhaps more
important in that it allows us to be precise about which values are
relevant at run time, and which are compile time only (that is, which are
erased). Using the ``0`` multiplicity means a function's type now tells us
exactly what it needs at run time.

For example, in Idris 1 you could get the length of a vector as follows

.. code-block:: idris

    vlen : Vect n a -> Nat
    vlen {n} xs = n
  
This is fine, since it runs in constant time, but the trade off is that
``n`` has to be available at run time, so at run time we always need the length
of the vector to be available if we ever call ``vlen``. Idris 1 can infer whether
the length is needed, but there's no easy way for a programmer to be sure.

In Idris 2, we need to state explicitly that ``n`` is needed at run time

.. code-block:: idris

    vlen : {n : Nat} -> Vect n a -> Nat
    vlen xs = n
  
(Incidentally, also note that in Idris 2, names bound in types are also available
in the definition without explicitly rebinding them.)

This also means that when you call ``vlen``, you need the length available. For
example, this will give an error

.. code-block:: idris

    sumLengths : Vect m a -> Vect n a —> Nat
    sumLengths xs ys = vlen xs + vlen ys
  
Idris 2 reports::

  vlen.idr:7:20--7:28:While processing right hand side of Main.sumLengths at vlen.idr:7:1--10:1:
  m is not accessible in this context
  
This means that it needs to use ``m`` as an argument to pass to ``vlen xs``,
where it needs to be available at run time, but ``m`` is not available in
``sumLengths`` because it has multiplicity ``0``.

We can see this more clearly by replacing the right hand side of
``sumLengths`` with a hole...

.. code-block:: idris

    sumLengths : Vect m a -> Vect n a -> Nat
    sumLengths xs ys = ?sumLengths_rhs
  
...then checking the hole's type at the REPL::

  Main> :t sumLengths_rhs
   0 n : Nat
   0 a : Type
   0 m : Nat
     ys : Vect n a
     xs : Vect m a
  -------------------------------------
  sumLengths_rhs : Nat

Instead, we need to give bindings for ``m`` and ``n`` with
unrestricted multiplicity

.. code-block:: idris

    sumLengths : {m, n : _} -> Vect m a -> Vect n a —> Nat
    sumLengths xs ys = vlen xs + vlen xs

Remember that giving no multiplicity on a binder, as with ``m`` and ``n`` here,
means that the variable has unrestricted usage.

If you're converting Idris 1 programs to work with Idris 2, this is probably the
biggest thing you need to think about. It is important to note,
though, that if you have bound implicits, such as...

.. code-block:: idris

    excitingFn : {t : _} -> Coffee t -> Moonbase t
   
...then it's a good idea to make sure ``t`` really is needed, or performance
might suffer due to the run time building the instance of ``t`` unnecessarily!

One final note on erasure: it is an error to try to pattern match on an
argument with multiplicity ``0``, unless its value is inferrable from
elsewhere. So, the following definition is rejected

.. code-block:: idris

    badNot : (0 x : Bool) -> Bool
    badNot False = True
    badNot True = False

This is rejected with the error::

  badnot.idr:2:1--3:1:Attempt to match on erased argument False in 
  Main.badNot

The following, however, is fine, because in ``sNot``, even though we appear
to match on the erased argument ``x``, its value is uniquely inferrable from
the type of the second argument

.. code-block:: idris

    data SBool : Bool -> Type where
         SFalse : SBool False
         STrue  : SBool True
  
    sNot : (0 x : Bool) -> SBool x -> Bool
    sNot False SFalse = True
    sNot True  STrue  = False

Experience with Idris 2 so far suggests that, most of the time, as long as
you're using unbound implicits in your Idris 1 programs, they will work without
much modification in Idris 2. The Idris 2 type checker will point out where you
require an unbound implicit argument at run time - sometimes this is both
surprising and enlightening!

.. _sect-pmtypes:

Pattern Matching on Types
-------------------------

One way to think about dependent types is to think of them as "first class"
objects in the language, in that they can be assigned to variables, 
passed around and returned from functions, just like any other construct.
But, if they're truly first class, we should be able to pattern match on
them too! Idris 2 allows us to do this. For example

.. code-block:: idris
 
    showType : Type -> String
    showType Int = "Int"
    showType (List a) = "List of " ++ showType a
    showType _ = "something else"

We can try this as follows::

  Main> showType Int
  "Int"
  Main> showType (List Int)
  "List of Int"
  Main> showType (List Bool)
  "List of something else"

Pattern matching on function types is interesting, because the return type
may depend on the input value. For example, let's add a case to
``showType``

.. code-block:: idris

  showType (Nat -> a) = ?help

Inspecting the type of ``help`` tells us::

  Main> :t help
     a : Nat -> Type
  -------------------------------------
  help : String

So, the return type ``a`` depends on the input value of type ``Nat``, and
we'll need to come up with a value to use ``a``, for example

.. code-block:: idris

    showType (Nat -> a) = "Function from Nat to " ++ showType (a Z)

Note that multiplicities on the binders, and the ability to pattern match
on *non-erased* types mean that the following two types are distinct

.. code-block:: idris

    id : a -> a
    notId : {a : Type} -> a -> a

In the case of ``notId``, we can match on ``a`` and get a function which
is certainly not the identity function

.. code-block:: idris

    notId {a = Int} x = x + 1
    notId x = x

::

  Main> notId 93
  94
  Main> notId "???"
  "???"

There is an important consequence of being able to distinguish between relevant
and irrelevant type arguments, which is that a function is *only* parametric in
``a`` if ``a`` has multiplicity ``0``. So, in the case of ``notId``, ``a`` is
*not* a parameter, and so we can't draw any conclusions about the way the
function will behave because it is polymorphic, because the type tells us it
might pattern match on ``a``.

On the other hand, it is merely a coincidence that, in non-dependently typed
languages, types are *irrelevant* and get erased, and values are *relevant*
and remain at run time. Idris 2, being based on QTT, allows us to make the
distinction between relevant and irrelevant arguments precise. Types can be
relevant, values (such as the ``n`` index to vectors) can be irrelevant.

For more details on multiplicities,
see `Idris 2: Quantitative Type Theory in Action <https://www.type-driven.org.uk/edwinb/idris-2-quantitative-type-theory-in-action.html>`_.
