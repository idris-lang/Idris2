************
FFI Overview
************

Foreign functions are declared with the ``%foreign`` directive, which takes the
following general form:

.. code-block:: idris

    %foreign [specifiers]
    name : t

The specifier is an Idris ``String`` which says in which language the foreign
function is written, what it's called, and where to find it. There may be more
than one specifier, and a code generator is free to choose any specifier it
understands - or even ignore the specifiers completely and use their own
approach. In general, a specifier has the form "Language:name,library". For
example, in C:

.. code-block:: idris

    %foreign "C:puts,libc"
    puts : String -> PrimIO Int

It is up to specific code generators to decide how to locate the function and
the library. In this document, we will assume the default Chez Scheme code
generator (the examples also work with the Racket or Gambit code generator) and
that the foreign language is C.

Example
-------

As a running example, we are going to work with a small C file. Save the
following content to a file ``smallc.c``

::

    #include <stdio.h>

    int add(int x, int y) {
        return x+y;
    }

    int addWithMessage(char* msg, int x, int y) {
        printf("%s: %d + %d = %d\n", msg, x, y, x+y);
        return x+y;
    }

Then, compile it to a shared library with::

    cc -shared smallc.c -o libsmall.so

We can now write an Idris program which calls each of these. First, we'll
write a small program which uses ``add`` to add two integers:

.. code-block:: idris

    %foreign "C:add,libsmall"
    add : Int -> Int -> Int
  
    main : IO ()
    main = printLn (add 70 24)

The ``%foreign`` declaration states that ``add`` is written in C, with the
name ``add`` in the library ``libsmall``. As long as the run time is able
to locate ``libsmall.so`` (in practice it looks in the current directory and
the system library paths) we can run this at the REPL:

::

    Main> :exec main
    94

Note that it is the programmer's responsibility to make sure that the
Idris function and C function have corresponding types. There is no way for
the machine to check this! If you get it wrong, you will get unpredictable
behaviour.

Since ``add`` has no side effects, we've given it a return type of ``Int``.
But what if the function has some effect on the outside world, like
``addWithMessage``? In this case, we use ``PrimIO Int`` to say that it
returns a primitive IO action:

.. code-block:: idris

    %foreign "C:addWithMessage,libsmall"
    prim_addWithMessage : String -> Int -> Int -> PrimIO Int

Internally, ``PrimIO Int`` is a function which takes the current (linear)
state of the world, and returns an ``Int`` with an updated state of the world.
We can convert this into an ``IO`` action using ``primIO``:

.. code-block:: idris

    primIO : PrimIO a -> IO a

So, we can extend our program as follows:

.. code-block:: idris

  addWithMessage : String -> Int -> Int -> IO Int
  addWithMessage s x y = primIO $ prim_addWithMessage s x y
  
  main : IO ()
  main
      = do printLn (add 70 24)
           addWithMessage "Sum" 70 24
           pure ()

It is up to the programmer to declare which functions are pure, and which have
side effects, via ``PrimIO``. Executing this gives:

::

    Main> :exec main
    94
    Sum: 70 + 24 = 94

We have seen two specifiers for foreign functions:

.. code-block:: idris

    %foreign "C:add,libsmall"
    %foreign "C:addWithMessage,libsmall"

These both have the same form: ``"C:[name],libsmall"`` so instead of writing
the concrete ``String``, we write a function to compute the specifier, and
use that instead:

.. code-block:: idris

    libsmall : String -> String
    libsmall fn = "C:" ++ fn ++ ",libsmall"

    %foreign (libsmall "add")
    add : Int -> Int -> Int

    %foreign (libsmall "addWithMessage")
    prim_addWithMessage : String -> Int -> Int -> PrimIO Int

.. _sect-ffi-string:

Primitive FFI Types
-------------------

The types which can be passed to and returned from foreign functions are
restricted to those which it is reasonable to assume any back end can handle.
In practice, this means most primitive types, and a limited selection of
others.  Argument types can be any of the following primitives:

* ``Int``
* ``Char``
* ``Double`` (as ``double`` in C)
* ``String`` (as ``char*`` in C)
* ``Ptr t`` and ``AnyPtr`` (both as ``void*`` in C)

Return types can be any of the above, plus:

* ``()``
* ``PrimIO t``, where ``t`` is a valid return type other than a ``PrimIO``.

Handling ``String`` leads to some complications, for a number of reasons:

* Strings can have multiple encodings. In the Idris run time, Strings are
  encoded as UTF-8, but C makes no assumptions.
* It is not always clear who is responsible for freeing a ``String`` allocated
  by a C function.
* In C, strings can be ``NULL``, but Idris strings always have a value.

So, when passing ``String`` to and from C, remember the following:

* A ``char*`` returned by a C function will be copied to the Idris heap, and
  the Idris run time immediately calls ``free`` with the returned ``char*``.
* If a ``char*`` might be ``NULL`` in ``C``, use ``Ptr String`` rather than
  ``String``.

When using ``Ptr String``, the value will be passed as a ``void*``, and
therefore not accessible directly by Idris code. This is to protect against
accidentally trying to use ``NULL`` as a ``String``. You can nevertheless
work with them and convert to ``String`` via foreign functions of the following
form:

::

    char* getString(void *p) {
        return (char*)p;
    }

    void* mkString(char* str) {
        return (void*)str;
    }

    int isNullString(void* str) {
        return str == NULL;
    }

For an example, see the sample :ref:`sect-readline` bindings.

Additionally, foreign functions can take *callbacks*, and take and return
C ``struct`` pointers.

.. _sect-callbacks:

Callbacks
---------

It is often useful in C for a function to take a *callback*, that is a function
which is called after doing some work. For example, we can write a function
which takes a callback that takes a ``char*`` and an ``int`` and returns a
``char*``, in C, as follows (added to ``smallc.c`` above):

::

    typedef char*(*StringFn)(char*, int);

    char* applyFn(char* x, int y, StringFn f) {
        printf("Applying callback to %s %d\n", x, y);
        return f(x, y);
    }

Then, we can access this from Idris by declaring it as a ``%foreign``
function and wrapping it in ``IO``, with the C function calling the Idris
function as the callback:

.. code-block:: idris

    %foreign (libsmall "applyFn")
    prim_applyFn : String -> Int -> (String -> Int -> String) -> PrimIO String
    
    applyFn : String -> Int -> (String -> Int -> String) -> IO String
    applyFn c i f = primIO $ prim_applyFn c i f

For example, we can try this as follows:

.. code-block:: idris

    pluralise : String -> Int -> String
    pluralise str x
        = show x ++ " " ++
                 if x == 1
                    then str
                    else str ++ "s"
    
    main : IO ()
    main
        = do str1 <- applyFn "Biscuit" 10 pluralise
             putStrLn str1
             str2 <- applyFn "Tree" 1 pluralise
             putStrLn str2

As a variant, the callback could have a side effect:

.. code-block:: idris

    %foreign (libsmall "applyFn")
    prim_applyFnIO : String -> Int -> (String -> Int -> PrimIO String) ->
                     PrimIO String
  
This is a little more fiddly to lift to an ``IO`` function, due to the callback,
but we can do so using ``toPrim : IO a -> PrimIO a``:
  
.. code-block:: idris

    applyFnIO : String -> Int -> (String -> Int -> IO String) -> IO String
    applyFnIO c i f = primIO $ prim_applyFnIO c i (\s, i => toPrim $ f s i)
  
For example, we can extend the above ``pluralise`` example to print a message
in the callback:

.. code-block:: idris

    pluralise : String -> Int -> IO String
    pluralise str x
        = do putStrLn "Pluralising"
             pure $ show x ++ " " ++
                    if x == 1
                       then str
                       else str ++ "s"
    
    main : IO ()
    main
        = do str1 <- applyFnIO "Biscuit" 10 pluralise
             putStrLn str1
             str2 <- applyFnIO "Tree" 1 pluralise
             putStrLn str2

Structs
-------

Many C APIs pass around more complex data structures, as a ``struct``.
We do not aim to be completely general in the C types we support, because
this will make it harder to write code which is portable across multiple
back ends. However, it is still often useful to be able to access a ``struct``
directly. For example, add the following to the top of ``smallc.c``, and
rebuild ``libsmall.so``:

::

    #include <stdlib.h>

    typedef struct {
        int x;
        int y;
    } point;

    point* mkPoint(int x, int y) {
        point* pt = malloc(sizeof(point));
        pt->x = x;
        pt->y = y;
        return pt;
    }

    void freePoint(point* pt) {
        free(pt);
    }

We can define a type for accessing ``point`` in Idris by importing
``System.FFI`` and using the ``Struct`` type, as follows:

.. code-block:: idris

    Point : Type
    Point = Struct "point" [("x", Int), ("y", Int)]
    
    %foreign (libsmall "mkPoint")
    mkPoint : Int -> Int -> Point
    
    %foreign (libsmall "freePoint")
    prim_freePoint : Point -> PrimIO ()
    
    freePoint : Point -> IO ()
    freePoint p = primIO $ prim_freePoint p

The ``Point`` type in Idris now corresponds to ``point*`` in C. Fields can
be read and written using the following, also from ``System.FFI``:

.. code-block:: idris

    getField : Struct s fs -> (n : String) ->
               FieldType n ty fs => ty
    setField : Struct s fs -> (n : String) ->
               FieldType n ty fs => ty -> IO ()

Notice that fields are accessed by name, and must be available in the
struct, given the constraint ``FieldType n ty fs``, which states that the
field named ``n`` has type ``ty`` in the structure fields ``fs``.
So, we can display a ``Point`` as follows by accessing the fields directly:

.. code-block:: idris

    showPoint : Point -> String
    showPoint pt
        = let x : Int = getField pt "x"
              y : Int = getField pt "y" in
              show (x, y)

And, as a complete example, we can initialise, update, display and
delete a ``Point`` as follows:

.. code-block:: idris

    main : IO ()
    main = do let pt = mkPoint 20 30
              setField pt "x" (the Int 40)
              putStrLn $ showPoint pt
              freePoint pt

The field types of a ``Struct`` can be any of the following:

* ``Int``
* ``Char``
* ``Double`` (``double`` in C)
* ``Ptr a`` or ``AnyPtr`` (``void*`` in C)
* Another ``Struct``, which is a pointer to a ``struct`` in C

Note that this doesn't include ``String`` or function types! This is primarily
because these aren't directly supported by the Chez back end. However, you can
use another pointer type and convert. For example, assuming you have, in C:

::

    typedef struct {
        char* name;
        point* pt;
    } namedpoint;

You can represent this in Idris as:

::

    NamedPoint : Type
    NamedPoint 
        = Struct "namedpoint" 
                   [("name", Ptr String),
                   ("pt", Point)]

That is, using a ``Ptr String`` instead of a ``String`` directly. Then you
can convert between a ``void*`` and a ``char*`` in C:

::

    char* getString(void *p) {
        return (char*)p;
    }

...and use this to convert to a ``String`` in Idris:

.. code-block:: idris

    %foreign (pfn "getString")
    getString : Ptr String -> String
