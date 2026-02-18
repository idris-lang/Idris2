Introducing App
===============

``App`` is declared as below, in a module ``Control.App``, which is part of
the ``base`` libraries.
It is parameterised by an implicit
``Path`` (which states whether the program's execution path
is linear or might throw
exceptions), which has a ``default`` value that the program
might throw, and a ``List Error``
(which gives a list of exception types which can be thrown, ``Error`` is
a synonym for ``Type``):

.. code-block:: idris

    data App : {default MayThrow l : Path} ->
               (es : List Error) -> Type -> Type

It serves the same purpose as ``IO``, but supports throwing and catching
exceptions, and allows us to define more constrained interfaces parameterised
by the list of errors ``es``.
e.g. a program which supports console IO:

.. code-block:: idris

    hello : Console es => App es ()
    hello = putStrLn "Hello, App world!"

We can use this in a complete program as follows:

.. code-block:: idris

    module Main

    import Control.App
    import Control.App.Console

    hello : Console es => App es ()
    hello = putStrLn "Hello, App world!"

    main : IO ()
    main = run hello

Or, a program which supports console IO and carries an ``Int`` state,
labelled ``Counter``:

.. code-block:: idris

    data Counter : Type where

    helloCount : (Console es, State Counter Int es) => App es ()
    helloCount = do c <- get Counter
                    put Counter (c + 1)
                    putStrLn "Hello, counting world"
                    c <- get Counter
                    putStrLn ("Counter " ++ show c)

To run this as part of a complete program, we need to initialise the state.

.. code-block:: idris

    main : IO ()
    main = run (new 93 helloCount)

For convenience, we can list multiple interfaces in one go, using a function
``Has``, defined in ``Control.App``, to compute the interface constraints:

.. code-block:: idris

    helloCount : Has [Console, State Counter Int] es => App es ()

    0 Has : List (a -> Type) -> a -> Type
    Has [] es = ()
    Has (e :: es') es = (e es, Has es' es)

The purpose of ``Path`` is to state whether a program can throw
exceptions, so that we can know where it is safe to reference linear
resources. It is declared as follows:

.. code-block:: idris

    data Path = MayThrow | NoThrow

The type of ``App`` states that ``MayThrow`` is the default.
We expect this to be the most
common case. After all, realistically, most operations have possible failure
modes, especially those which interact with the outside world.

The ``0`` on the declaration of ``Has`` indicates that it can only
be run in an erased context, so it will never be run at run-time.
To run an ``App`` inside ``IO``, we use an initial
list of errors ``Init`` (recall that an ``Error`` is a
synonym for ``Type``):

.. code-block:: idris

    Init : List Error
    Init = [AppHasIO]

    run : App {l} Init a -> IO a

Generalising the ``Path`` parameter with ``l``
means that we can invoke ``run`` for any application, whether the ``Path``
is ``NoThrow`` or ``MayThrow``. But, in practice, all applications
given to ``run`` will not throw at the top level, because the only
exception type available is the type ``AppHasIO``, which is an empty data
type (it has no values). Any exceptions will have been introduced and handled
inside the ``App``.
