Defining Interfaces
===================

The only way provided by ``Control.App`` to run an ``App`` is
via the ``run`` function, which takes a concrete list of errors
``Init``.
All concrete extensions to this list of errors are via either ``handle``,
to introduce a new exception, or ``new``, to introduce a new state.
In order to compose ``App`` programs effectively, rather than
introducing concrete exceptions and state in general, we define interfaces for
collections of operations which work in a specific list of errors.

Example: Console I/O
--------------------

We have seen an initial example using the ``Console`` interface,
which is declared as follows, in ``Control.App.Console``:

.. code-block:: idris

    interface Console e where
      putChar : Char -> App {l} e ()
      putStr : String -> App {l} e ()
      getChar : App {l} e Char
      getLine : App {l} e String

It provides primitives for writing to and reading from the console, and
generalising the path parameter to ``l`` means that neither can
throw an exception, because they have to work in both the ``NoThrow``
and ``MayThrow`` contexts.

To implement this for use in a top level ``IO``
program, we need access to primitive ``IO`` operations.
The ``Control.App`` library defines a primitive interface for this:

.. code-block:: idris

    interface PrimIO e where
      primIO : IO a -> App {l} e a
      fork : (forall e' . PrimIO e' => App {l} e' ()) -> App e ()

We use ``primIO`` to invoke an ``IO`` function. We also have a ``fork``
primitive, which starts a new thread in a new list of errors supporting
``PrimIO``.  Note that ``fork`` starts a new list of errors ``e'`` so that states
are only available in a single thread.

There is an implementation of ``PrimIO`` for a list of errors which can
throw the empty type as an exception. This means that if ``PrimIO``
is the only interface available, we cannot throw an exception, which is
consistent with the definition of ``IO``. This also allows us to
use ``PrimIO`` in the initial list of errors ``Init``.

.. code-block:: idris

    HasErr AppHasIO e => PrimIO e where ...

Given this, we can implement ``Console`` and run our ``hello``
program in ``IO``. It is implemented as follows in ``Control.App.Console``:

.. code-block:: idris

    PrimIO e => Console e where
      putChar c = primIO $ putChar c
      putStr str = primIO $ putStr str
      getChar = primIO getChar
      getLine = primIO getLine

Example: File I/O
-----------------

Console I/O can be implemented directly, but most I/O operations can fail.
For example, opening a file can fail for several reasons: the file does not
exist; the user has the wrong permissions, etc. In Idris, the ``IO``
primitive reflects this in its type:

.. code-block:: idris

    openFile : String -> Mode -> IO (Either FileError File)

While precise, this becomes unwieldy when there are long sequences of
``IO`` operations. Using ``App``, we can provide an interface
which throws an exception when an operation fails, and guarantee that any
exceptions are handled at the top level using ``handle``.
We begin by defining the ``FileIO`` interface, in ``Control.App.FileIO``:

.. code-block:: idris

    interface Has [Exception IOError] e => FileIO e where
      withFile : String -> Mode ->
                 (onError : IOError -> App e a) ->
                 (onOpen : File -> App e a) ->
                 App e a
      fGetStr : File -> App e String
      fGetChars : File -> Int -> App e String
      fGetChar : File -> App e Char
      fPutStr : File -> String -> App e ()
      fPutStrLn : File -> String -> App e ()
      fflush : File -> App e ()
      fEOF : File -> App e Bool

We use resource bracketing - passing a function to ``withFile`` for working
with the opened file - rather than an explicit ``open`` operation,
to open a file, to ensure that the file handle is cleaned up on
completion.

One could also imagine an interface using a linear resource for the file, which
might be appropriate in some safety critical contexts, but for most programming
tasks, exceptions should suffice.
All of the operations can fail, and the interface makes this explicit by
saying we can only implement ``FileIO`` if the list of errors supports
throwing and catching the ``IOError`` exception. ``IOError`` is defined
in ``Control.App``.

For example, we can use this interface to implement ``readFile``, throwing
an exception if opening the file fails in ``withFile``:

.. code-block:: idris

    readFile : FileIO e => String -> App e String
    readFile f = withFile f Read throw $ \h =>
                   do content <- read [] h
                      pure (concat content)
    where
      read : List String -> File -> App e (List String)
      read acc h = do eof <- fEOF h
                      if eof then pure (reverse acc)
                             else do str <- fGetStr h
                                     read (str :: acc) h

Again, this is defined in ``Control.App.FileIO``.

To implement ``FileIO``, we need access to the primitive operations
via ``PrimIO``, and the ability to throw exceptions if any of the
operations fail. With this, we can implement ``withFile`` as follows,
for example:

.. code-block:: idris

    Has [PrimIO, Exception IOError] e => FileIO e where
      withFile fname m onError proc
          = do Right h <- primIO $ openFile fname m
                  | Left err => onError (FileErr (toFileEx err))
               res <- catch (proc h) onError
               primIO $ closeFile h
               pure res
      ...

Given this implementation of ``FileIO``, we can run ``readFile``,
provided that we wrap it in a top level ``handle`` function to deal
with any errors thrown by ``readFile``:

.. code-block:: idris

    readMain : String -> App Init ()
    readMain fname = handle (readFile fname)
           (\str => putStrLn $ "Success:\n" ++ show str)
           (\err : IOError => putStrLn $ "Error: " ++ show err)
