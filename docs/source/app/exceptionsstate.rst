Exceptions and State
====================

``Control.App`` is primarily intended to make it easier to manage the common
cases of applications with exceptions and state. We can throw and catch
exceptions listed in the list of errors (the ``es`` parameter to ``App``) and
introduce new global state.

Exceptions
----------

The ``List Error`` is a list of error types, which can be thrown and caught
using the functions below:

.. code-block:: idris

    throw : HasErr err es => err -> App es a
    catch : HasErr err es => App es a -> (err -> App es a) -> App es a

We can use ``throw`` and ``catch`` for some exception type ``err`` as 
long as the exception type exists in the list of errors, ``es``, as 
checked by the ``HasErr`` predicate, also defined in ``Control.App`` 
(Also, note that ``Exception`` is a synonym for ``HasErr``):

.. code-block:: idris

    data HasErr : Error -> List Error -> Type where
         Here : HasErr e (e :: es)
         There : HasErr e es -> HasErr e (e' :: es)
    
    Exception : Error -> List Error -> Type
    Exception = HasErr

Finally, we can introduce new exception types via ``handle``, which runs a
block of code which might throw, handling any exceptions:

.. code-block:: idris

    handle : App (err :: e) a ->
             (onok : a -> App e b) ->
             (onerr : err -> App e b) -> App e b

Adding State
------------

Applications will typically need to keep track of state, and we support
this primitively in ``App`` using a ``State`` type, defined in
``Control.App``:

.. code-block:: idris

    data State : (tag : a) -> Type -> List Error -> Type

The ``tag`` is used purely to distinguish between different states,
and is not required at run-time, as explicitly stated in the types of
``get`` and ``put``, which are used to access and update a state:

.. code-block:: idris

    get : (0 tag : _) -> State tag t e => App {l} e t
    put : (0 tag : _) -> State tag t e => (1 val : t) -> App {l} e ()

These use an ``auto``-implicit to pass around
a ``State`` with the relevant ``tag`` implicitly, so we refer
to states by tag alone. In ``helloCount`` earlier, we used an empty type
``Counter`` as the tag:

.. code-block:: idris

    data Counter : Type where -- complete definition

The list of errors ``e`` is used to ensure that
states are only usable in the list of errors in which they are introduced.
States are introduced using ``new``:

.. code-block:: idris

    new : t -> (1 p : State tag t e => App {l} e a) -> App {l} e a

Note that the type tells us ``new`` runs the program with the state
exactly once.
Rather than using ``State`` and ``Exception`` directly, however,
we typically use interfaces to constrain the operations which are allowed
in a list of errors. Internally, ``State`` is implemented via an
``IORef``, primarily for performance reasons.
