.. _sect-readline:

**********************************
Example: Minimal Readline Bindings
**********************************

In this section, we'll see how to create bindings for a C library (the `GNU
Readline <https://tiswww.case.edu/php/chet/readline/rltop.html>`_ library) in
Idris, and make them available in a package. We'll only create the most minimal
bindings, but nevertheless they demonstrate some of the trickier problems in
creating bindings to a C library, in that they need to handle memory allocation
of ``String``.

You can find the example in full in the Idris 2 source repository, 
in `samples/FFI-readline
<https://github.com/edwinb/Idris2/tree/master/samples/FFI-readline>`_. As a
minimal example, this can be used as a starting point for other C library
bindings.

We are going to provide bindings to the following functions in the Readline
API, available via ``#include <readline/readline.h>``:

::

    char* readline (const char *prompt);
    void add_history(const char *string);

Additionally, we are going to support tab completion, which in the Readline
API is achieved by setting a global variable to a callback function
(see Section :ref:`sect-callbacks`) which explains how to handle the
completion:

::

    typedef char *rl_compentry_func_t (const char *, int);
    rl_compentry_func_t * rl_completion_entry_function;

A completion function takes a ``String``, which is the text to complete, and
an ``Int``, which is the number of times it has asked for a completion so far.
In Idris, this could be a function ``complete : String -> Int -> IO String``.
So, for example, if the text so far is ``"id"``, and the possible completions
are ``idiomatic`` and ``idris``, then ``complete "id" 0`` would produce the
string ``"idiomatic"`` and ``complete "id" 1`` would produce ``"idris"``.

We will define *glue* functions in a C file ``idris_readline.c``, which compiles
to a shared object ``libidrisreadline``, so we write a function for locating
the C functions:

.. code-block:: idris

    rlib : String -> String
    rlib fn = "C:" ++ fn ++ ",libidrisreadline"

Each of the foreign bindings will have a ``%foreign`` specifier which locates
functions via ``rlib``.

Basic behaviour: Reading input, and history
-------------------------------------------

We can start by writing a binding for ``readline`` directly. It's interactive,
so needs to return a ``PrimIO``:

.. code-block:: idris

    %foreign (rlib "readline")
    prim_readline : String -> PrimIO String

Then, we can write an ``IO`` wrapper:

.. code-block:: idris

    readline : String -> IO String
    readline prompt = primIO $ readline prompt

Unfortunately, this isn't quite good enough! The C ``readline`` function
returns a ``NULL`` string if there is no input due to encountering an
end of file. So, we need to handle that - if we don't, we'll get a crash
on encountering end of file (remember: it's the Idris programmer's responsibility
to give an appropriate type to the C binding!)

Instead, we need to use a ``Ptr`` to say that it might be a ``NULL``
pointer (see Section :ref:`sect-ffi-string`):

.. code-block:: idris

    %foreign (rlib "readline")
    prim_readline : String -> PrimIO (Ptr String)

We also need to provide a way to check whether the returned ``Ptr String`` is 
``NULL``. To do so, we'll write some glue code to convert back and forth
between ``Ptr String`` and ``String``, in a file ``idris_readline.c`` and a
corresponding header ``idris_readline.h``. In ``idris_readline.h`` we have:

::

    int isNullString(void* str); // return 0 if a string in NULL, non zero otherwise
    char* getString(void* str); // turn a non-NULL Ptr String into a String (assuming not NULL)
    void* mkString(char* str); // turn a String into a Ptr String
    void* nullString(); // create a new NULL String

Correspondingly, in ``idris_readline.c``:

::

    int isNullString(void* str) {
        return str == NULL;
    }

    char* getString(void* str) {
        return (char*)str;
    }

    void* mkString(char* str) {
        return (void*)str;
    }

    void* nullString() {
        return NULL;
    }

Now, we can use ``prim_readline`` as follows, with a safe API, checking
whether the result it returns is ``NULL`` or a concrete ``String``:

.. code-block:: idris

    %foreign (rlib "isNullString")
    prim_isNullString : Ptr String -> Int

    export
    isNullString : Ptr String -> Bool
    isNullString str = if prim_isNullString str == 0 then False else True

    export
    readline : String -> IO (Maybe String)
    readline s
        = do mstr <- primIO $ prim_readline s
             if isNullString mstr
                then pure $ Nothing
                else pure $ Just (getString mstr)

We'll need ``nullString`` and ``mkString`` later, for dealing with completions.

Once we've read a string, we'll want to add it to the input history. We can
provide a binding to ``add_history`` as follows:

.. code-block:: idris

    %foreign (rlib "add_history")
    prim_add_history : String -> PrimIO ()

    export
    addHistory : String -> IO ()
    addHistory s = primIO $ prim_add_history s

In this case, since Idris is in control of the ``String``, we know it's not
going to be ``NULL``, so we can add it directly.

A small ``readline`` program that reads input, and echoes it, recording input
history for non-empty inputs, can be written as follows:

.. code-block:: idris

    echoLoop : IO ()
    echoLoop 
        = do Just x <- readline "> "
                  | Nothing => putStrLn "EOF"
             putStrLn ("Read: " ++ x)
             when (x /= "") $ addHistory x
             if x /= "quit"
                then echoLoop
                else putStrLn "Done"

This gives us command history, and command line editing, but Readline becomes
much more useful when we add tab completion. The default tab completion, which
is available even in the small example above, is to tab complete file names
in the current working directory. But for any realistic application, we probably
want to tab complete other commands, such as function names, references to
local data, or anything that is appropriate for the application.

Completions
-----------

Readline has a large API, with several ways of supporting tab completion,
typically involving setting a global variable to an appropriate completion
function. We'll use the following:

::

    typedef char *rl_compentry_func_t (const char *, int);
    rl_compentry_func_t * rl_completion_entry_function;

The completion function takes the prefix of the completion, and the number
of times it has been called so far on this prefix, and returns the next
completion, or ``NULL`` if there are no more completions. An Idris equivalent
would therefore have the following type:

.. code-block:: idris

    setCompletionFn : (String -> Int -> IO (Maybe String)) -> IO ()

The function returns ``Nothing`` if there are no more completions, or
``Just str`` for some ``str`` if there is another one for the current
input.

We might hope that it's a matter of defining a function to assign the
completion function...

::

    void idrisrl_setCompletion(rl_compentry_func_t* fn) {
        rl_completion_entry_function = fn;
    }

...then defining the Idris binding, which needs to take into account that
the Readline library expects ``NULL`` when there are no more completions:

.. code-block:: idris

    %foreign (rlib "idrisrl_setCompletion")
    prim_setCompletion : (String -> Int -> PrimIO (Ptr String)) -> PrimIO ()

    export
    setCompletionFn : (String -> Int -> IO (Maybe String)) -> IO ()
    setCompletionFn fn
        = primIO $ prim_setCompletion $ \s, i => toPrim $
              do mstr <- fn s i
                 case mstr of
                      Nothing => pure nullString // need to return a Ptr String to readline!
                      Just str => pure (mkString str)

So, we turn ``Nothing`` into ``nullString`` and ``Just str`` into ``mkString
str``. Unfortunately, this doesn't quite work. To see what goes wrong, let's
try it for the most basic completion function that returns one completion no
matter what the input:

.. code-block:: idris

    testComplete : String -> Int -> IO (Maybe String)
    testComplete text 0 = pure $ Just "hamster"
    testComplete text st = pure Nothing

We'll try this in a small modification of ``echoLoop`` above, setting a
completion function first:

.. code-block :: idris

    main : IO ()
    main = do setCompletionFn testComplete
              echoLoop

We see that there is a problem when we try running it, and hitting TAB before
entering anything:

::

    Main> :exec main
    > free(): invalid pointer

The Idris code which sets up the completion is fine, but there is a problem
with the memory allocation in the C glue code.

This problem arises because we haven't thought carefully enough about which
parts of our program are responsible for allocating and freeing strings.
When Idris calls a foreign function that returns a string, it copies the
string to the Idris heap and frees it immediately. But, if the foreign
library also frees the string, it ends up being freed twice. This is what's
happening here: the callback passed to ``prim_setCompletion`` frees the string
and puts it onto the Idris heap, but Readline also frees the string returned
by ``prim_setCompletion`` once it has processed it. We can solve this
problem by writing a wrapper for the completion function which reallocates
the string, and using that in ``idrisrl_setCompletion`` instead.

::

    rl_compentry_func_t* my_compentry;

    char* compentry_wrapper(const char* text, int i) {
        char* res = my_compentry(text, i); // my_compentry is an Idris function, so res is on the Idris heap,
                                           // and freed on return
        if (res != NULL) {
            char* comp = malloc(strlen(res)+1); // comp is passed back to readline, which frees it when
                                                // it is finished with it
            strcpy(comp, res);
            return comp;
        }
        else {
            return NULL;
        }
    }

    void idrisrl_setCompletion(rl_compentry_func_t* fn) {
        rl_completion_entry_function = compentry_wrapper;
        my_compentry = fn; // fn is an Idris function, called by compentry_wrapper
    }

So, we define the completion function in C, which calls the Idris completion
function then makes sure the string returned by the Idris function is copied
to the C heap.

We now have a primitive API that covers the most fundamental features of the
readline API:

.. code-block:: idris

    readline : String -> IO (Maybe String)
    addHistory : String -> IO ()
    setCompletionFn : (String -> Int -> IO (Maybe String)) -> IO ()
