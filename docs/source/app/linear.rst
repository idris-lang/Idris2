Linear Resources
================

We have introduced ``App`` for writing
interactive programs, using interfaces to constrain which operations are
permitted, but have not yet seen the ``Path`` parameter in action.
Its purpose is to constrain when programs can throw exceptions,
to know where linear resource usage is allowed. The bind operator
for ``App`` is defined as follows (not via ``Monad``):

.. code-block:: idris

    data SafeBind : Path -> (l' : Path) -> Type where
         SafeSame : SafeBind l l
         SafeToThrow : SafeBind NoThrow MayThrow

    (>>=) : SafeBind l l' =>
            App {l} e a -> (a -> App {l=l'} e b) -> App {l=l'} e b

The intuition behind this type is that, when sequencing two ``App``
programs:

* if the first action might throw an exception, then the whole program might
  throw.
* if the first action cannot throw an exception, the second action can still
  throw, and the program as a whole can throw.
* if neither action can throw an exception, the program as a whole cannot
  throw.

The reason for the detail in the type is that it is useful to be able to
sequence programs with a different ``Path``, but in doing so, we must
calculate the resulting ``Path`` accurately.
Then, if we want to sequence subprograms with linear variables,
we can use an alternative bind operator which guarantees to run the
continuation exactly once:

.. code-block:: idris

    bindL : App {l=NoThrow} e a ->
            (1 k : a -> App {l} e b) -> App {l} e b

To illustrate the need for ``bindL``, we can try writing a program which
tracks the state of a secure data store, which requires logging in before
reading the data.

Example: a data store requiring a login
---------------------------------------

Many software components rely on some form of state, and there may be
operations which are only valid in specific states. For example, consider
a secure data store in which a user must log in before getting access to
some secret data. This system can be in one of two states:

* ``LoggedIn``, in which the user is allowed to read the secret
* ``LoggedOut``, in which the user has no access to the secret

We can provide commands to log in, log out, and read the data, as illustrated
in the following diagram:

|login|

The ``login`` command, if it succeeds, moves the overall system state from
``LoggedOut`` to ``LoggedIn``. The ``logout`` command moves the state from
``LoggedIn`` to ``LoggedOut``. Most importantly, the ``readSecret`` command
is only valid when the system is in the ``LoggedIn`` state.

We can represent the state transitions using functions with linear types.
To begin, we define an interface for connecting to and disconnecting from
a store:

.. code-block:: idris

    interface StoreI e where
        connect : (1 prog : (1 d : Store LoggedOut) ->
                  App {l} e ()) -> App {l} e ()
        disconnect : (1 d : Store LoggedOut) -> App {l} e ()

Neither ``connect`` nor ``disconnect`` throw, as shown by
generalising over ``l``. Once we
have a connection, we can use the following functions to
access the resource directly:

.. code-block:: idris

    data Res : (a : Type) -> (a -> Type) -> Type where
         (#) : (val : a) -> (1 resource : r val) -> Res a r

    login : (1 s : Store LoggedOut) -> (password : String) ->
            Res Bool (\ok => Store (if ok then LoggedIn else LoggedOut))
    logout : (1 s : Store LoggedIn) -> Store LoggedOut
    readSecret : (1 s : Store LoggedIn) ->
                 Res String (const (Store LoggedIn))

``Res`` is defined in the Prelude, since it is commonly useful.  It is a
dependent pair type, which associates a value with a linear resource.
We'll leave the other definitions abstract, for the purposes of this
introductory example.

The following listing shows a complete program accessing the store, which
reads a password, accesses the store if the password is correct and prints the
secret data. It uses ``let (>>=) = bindL`` and ``(>>) = seqL`` to redefine
``do``-notation locally.

.. code-block:: idris

    storeProg : Has [Console, StoreI] e => App e ()
    storeProg = let (>>=) = bindL
                    (>>) = seqL in
          do putStr "Password: "
             password <- getStr
             connect $ \s =>
               do let True # s = login s password
                    | False # s => do putStrLn "Wrong password"
                                      disconnect s
                  let str # s = readSecret s
                  putStrLn $ "Secret: " ++ show str
                  let s = logout s
                  disconnect s

If we omit the ``let (>>=) = bindL``, it will use the default
``(>>=)`` operator, which allows the continuation to be run multiple
times, which would mean that ``s`` is not guaranteed to be accessed
linearly, and ``storeProg`` would not type check (and similarly
with ``(>>) = bindIg``).
We can safely use ``getStr`` and ``putStr`` because they
are guaranteed not to throw by the ``Path`` parameter in their types.

.. |login| image:: ../image/login.png
                   :width: 500px

App1: Linear Interfaces
-----------------------

Adding the ``bindL`` function to allow locally rebinding the
``(>>=)`` operator allows us to combine existing linear resource
programs with operations in ``App`` - at least, those that don't throw.
It would nevertheless be nice to interoperate more directly with ``App``.
One advantage of defining interfaces is that we can provide multiple
implementations for different contexts, but our implementation of the
data store uses primitive functions (which we left undefined in any case)
to access the store.

To allow control over linear resources, ``Control.App`` provides an alternative
parameterised type ``App1``:

.. code-block:: idris

    data App1 : {default One u : Usage} ->
                (es : List Error) -> Type -> Type

There is no need for a ``Path`` argument, since linear programs can
never throw. The ``Usage`` argument states whether the value
returned is to be used once, or has unrestricted usage, with
the default in ``App1`` being to use once:

.. code-block:: idris

    data Usage = One | Any

The main difference from ``App`` is the ``(>>=)`` operator, which
has a different multiplicity for the variable bound by the continuation
depending on the usage of the first action:

.. code-block:: idris

    Cont1Type : Usage -> Type -> Usage -> List Error -> Type -> Type
    Cont1Type One a u e b = (1 x : a) -> App1 {u} e b
    Cont1Type Any a u e b = (x : a) -> App1 {u} e b

    (>>=) : {u : _} -> (1 act : App1 {u} e a) ->
            (1 k : Cont1Type u a u' e b) -> App1 {u=u'} e b

``Cont1Type`` returns a continuation which uses the argument linearly,
if the first ``App1`` program has usage ``One``, otherwise it
returns a continuation where argument usage is unrestricted. Either way,
because there may be linear resources in scope, the continuation is
run exactly once and there can be no exceptions thrown.

Using ``App1``, we can define all of the data store operations in a
single interface, as shown in the following listing.
Each operation other than ``disconnect`` returns a `linear` resource.

.. code-block:: idris

    interface StoreI e where
      connect : App1 e (Store LoggedOut)
      login : (1 d : Store LoggedOut) -> (password : String) ->
              App1 e (Res Bool (\ok => Store (if ok then LoggedIn
                                                    else LoggedOut))
      logout : (1 d : Store LoggedIn) -> App1 e (Store LoggedOut)
      readSecret : (1 d : Store LoggedIn) ->
                   App1 e (Res String (const (Store LoggedIn)))
      disconnect : (1 d : Store LoggedOut) -> App {l} e ()

We can explicitly move between ``App`` and ``App1``:

.. code-block:: idris

    app : (1 p : App {l=NoThrow} e a) -> App1 {u=Any} e a
    app1 : (1 p : App1 {u=Any} e a) -> App {l} e a

We can run an ``App`` program using ``app``, inside ``App1``,
provided that it is guaranteed not to throw. Similarly, we can run an
``App1`` program using ``app1``, inside ``App``, provided that
the value it returns has unrestricted usage. So, for example, we can
write:

.. code-block:: idris

    storeProg : Has [Console, StoreI] e => App e ()
    storeProg = app1 $ do
         store <- connect
         app $ putStr "Password: "
         ?what_next

This uses ``app1`` to state that the body of the program is linear,
then ``app`` to state that the ``putStr`` operation is in
``App``. We can see that ``connect`` returns a linear resource
by inspecting the hole ``what_next``, which also shows that we are
running inside ``App1``:

.. code-block:: idris

     0 e : List Type
     1 store : Store LoggedOut
    -------------------------------------
    what_next : App1 e ()

For completeness, one way to implement the interface is as follows, with
hard coded password and internal data:

.. code-block:: idris

    Has [Console] e => StoreI e where
      connect
          = do app $ putStrLn "Connect"
               pure1 (MkStore "xyzzy")

      login (MkStore str) pwd
          = if pwd == "Mornington Crescent"
               then pure1 (True # MkStore str)
               else pure1 (False # MkStore str)
      logout (MkStore str) = pure1 (MkStore str)
      readSecret (MkStore str) = pure1 (str # MkStore str)

      disconnect (MkStore _)
          = putStrLn "Disconnect"

Then we can run it in ``main``:

.. code-block:: idris

    main : IO ()
    main = run storeProg
