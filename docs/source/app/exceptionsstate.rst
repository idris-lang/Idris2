Exceptions and State
====================

``Control.App`` is primarily intended to make it easier to manage the common
cases of applications with exceptions and state. We can throw and catch
exceptions listed in the environment (the ``e`` parameter to ``App``) and
introduce new global state.

Exceptions
----------

The ``Environment`` is a list of error types, usable via the
``Exception`` interface defined in ``Control.App``:

.. code-block:: idris

    interface Exception err e where
      throw : err -> App e a
      catch : App e a -> (err -> App e a) -> App e a

We can use ``throw`` and ``catch`` for some exception type
``err`` as long as the exception type exists in the environment. This is
checked with the ``HasErr`` predicate, also defined in ``Control.App``:

.. code-block:: idris

    data HasErr : Type -> Environment -> Type where
         Here : HasErr e (e :: es)
         There : HasErr e es -> HasErr e (e' :: es)

    HasErr err e => Exception err e where ...

Note the ``HasErr`` constraint on ``Exception``: this is one place
where it is notationally convenient that the ``auto`` implicit mechanism
and the interface resolution mechanism are identical in Idris 2.
Finally, we can introduce new exception types via ``handle``, which runs a
block of code which might throw, handling any exceptions:

.. code-block:: idris

    handle : App (err :: e) a -> (onok : a -> App e b) ->
             (onerr : err -> App e b) -> App e b

Adding State
------------

Applications will typically need to keep track of state, and we support
this primitively in ``App`` using a ``State`` type, defined in
``Control.App``:

.. code-block:: idris

    data State : (tag : a) -> Type -> Environment -> Type

The ``tag`` is used purely to distinguish between different states,
and is not required at run-time, as explicitly stated in the types of
``get`` and ``put``, which are used to access and update a state:

.. code-block:: idris

    get : (0 tag : a) -> State tag t e => App {l} e t
    put : (0 tag : a) -> State tag t e => t -> App {l} e ()

These use an ``auto``-implicit to pass around
a ``State`` with the relevant ``tag`` implicitly, so we refer
to states by tag alone. In ``helloCount`` earlier, we used an empty type
\texttt{Counter} as the tag:

.. code-block:: idris

    data Counter : Type where -- complete definition

The environment ``e`` is used to ensure that
states are only usable in the environment in which they are introduced.
States are introduced using ``new``:

.. code-block:: idris

    new : t -> (1 p : State tag t e => App {l} e a) -> App {l} e a

Note that the type tells us ``new`` runs the program with the state
exactly once.
Rather than using ``State`` and ``Exception`` directly, however,
we typically use interfaces to constrain the operations which are allowed
in an environment. Internally, ``State`` is implemented via an
``IORef``, primarily for performance reasons.


