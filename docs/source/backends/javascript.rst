***********************************
Javascript and Node Code Generators
***********************************

There are two javascript code generators, ``node`` and ``javascript``. There are two
differences between the two: the ``javascript`` code generator when called to
output an HTML file will also generate a basic HTML document with the
generated code inside a ``<script>`` tag; the other distinction is on the ffi
that will be explained below.


Javascript FFI Specifiers
=========================

There are three main kinds of javascript ffi specifiers ``javascript``,
``node`` and ``browser``. ``javascript`` is for foreigns that are available on
node and the browser, ``node`` for foreigns that are only available on node and
``browser`` for browser only foreigns.

For ``node`` there are two ways of defining a foreign:

.. code-block:: idris

    %foreign "node:lambda: n => process.env[n]"
    prim_getEnv : String -> PrimIO (Ptr String)

here ``lambda`` means that we are providing the definition as a lambda
expression.


.. code-block:: idris

    %foreign "node:lambda:fp=>require('fs').fstatSync(fp.fd, {bigint: false}).size"
    prim__fileSize : FilePtr -> PrimIO Int

``require`` can be used to import javascript modules.

For completion below an example of a foreign available only with ``browser`` codegen:

.. code-block:: idris

    %foreign "browser:lambda:x=>{document.body.innerHTML = x}"
    prim__setBodyInnerHTML : String -> PrimIO ()


Short Example
-------------

An interesting example is creating a foreign for the setTimeout function:

.. code-block:: idris

    %foreign "javascript:lambda:(callback, delay)=>setTimeout(callback, delay)"
    prim__setTimeout : (PrimIO ()) -> Int -> PrimIO ()

    setTimeout : HasIO io => IO () -> Int -> io ()
    setTimeout callback delay = primIO $ prim__setTimeout (toPrim callback) delay

Note: Previous versions of the javascript backends treated ``Int`` as a
64 bit signed integer represented by ``BigInt`` in javascript land. This is no
longer the case: ``Int`` is now treated as a 32 bit signed integer represented
by ``Number``. This should facilitate interop between Idris2 and the backend.

However, unless you have good reasons to do otherwise, consider using
one of the other fixed precision integral types. They are supposed to behave
the same across all backends. All signed and unsigned integrals of up to
32 bit precision (``Int8``, ``Int16``, ``Int32``, ``Bits8``, ``Bits16``, and ``Bits32``)
are represented by ``Number`` while ``Int64``, ``Bits64``, and ``Integer``
are represented by ``BigInt``. The example above could therefore be
improved by using ``Int32`` instad of ``Int``:

.. code-block:: idris

    %foreign "javascript:lambda:(callback, delay)=>setTimeout(callback, delay)"
    prim__setTimeout : (PrimIO ()) -> Int32 -> PrimIO ()

    setTimeout : HasIO io => IO () -> Int32 -> io ()
    setTimeout callback delay = primIO $ prim__setTimeout (toPrim callback) delay

Browser Example
===============

To build JavaScript aimed to use in the browser, the code must be compiled with
the javascript codegen option. The compiler produces a JavaScript or an HTML file.
The browser needs an HTML file to load. This HTML file can be created in two ways

- If the ``.html`` suffix is given to the output file the compiler generates an HTML file
  which includes a wrapping around the generated JavaScript.
- If *no* ``.html`` suffix is given, the generated file only contains the JavaScript code.
  In this case manual wrapping is needed.

Example of the wrapper HTML:

.. code-block:: html

    <html>
     <head><meta charset='utf-8'></head>
     <body>
      <script type='text/javascript'>
      JS code goes here
      </script>
     </body>
    </html>

As our intention is to develop something that runs in the browser questions naturally arise:

- How to interact with HTML elements?
- More importantly, when does the generated Idris code start?

Starting point of the Idris generated code
------------------------------------------

The generated JavaScript for your program contains an entry point. The ``main`` function is compiled
to a JavaScript top-level expression, which will be evaluated during the loading of the ``script``
tag and that is the entry point for Idris generated program starting in the browser.

Interaction with HTML elements
------------------------------

As sketched in the Short Example section, the FFI must be used when interaction happens between Idris
generated code and the rest of the Browser/JS ecosystem. Information handled by the FFI is
separated into two categories. Primitive types in Idris FFI, such as Int, and everything else.
The everything else part is accessed via AnyPtr. The ``%foreign`` construction should be used
to give implementation on the JavaScript side. And an Idris function declaration  to give ``Type``
declaration on the Idris side. The syntax is ``%foreign "browser:lambda:js-lambda-expression"`` .
On the Idris side, primitive types and ``PrimIO t`` types should be used as parameters,
when defining ``%foreign``. This declaration is a helper function which needs to be called
behind the ``primIO`` function. More on this can be found in the FFI chapter.

Examples for JavaScript FFI
---------------------------

console.log
-----------

.. code-block:: idris

    %foreign "browser:lambda: x => console.log(x)"
    prim__consoleLog : String -> PrimIO ()

    consoleLog : HasIO io => String -> io ()
    consoleLog x = primIO $ prim__consoleLog x

String is a primitive type in Idris and it is represented as a JavaScript String. There is no need
for any conversion between the Idris and the JavaScript.

setInterval
-----------

.. code-block:: idris

    %foreign "browser:lambda: (a,i)=>setInterval(a,i)"
    prim__setInterval : PrimIO () -> Int32 -> PrimIO ()

    setInterval : (HasIO io) => IO () -> Int32 -> io ()
    setInterval a i = primIO $ prim__setInterval (toPrim a) i

The ``setInterval`` JavaScript function executes the given function in every ``x`` millisecond.
We can use Idris generated functions in the callback as far as they have the type ``IO ()`` .

HTML Dom elements
-----------------

Lets turn our attention to the Dom elements and events. As said above, anything that is not a
primitive type should be handled via the ``AnyPtr`` type in the FFI. Anything complex that is
returned by a JavaScript function should be captured in an ``AnyPtr`` value. It is advisory to
separate the ``AnyPtr`` values into categories.

.. code-block:: idris

    data DomNode = MkNode AnyPtr

    %foreign "browser:lambda: () => document.body"
    prim__body : () -> PrimIO AnyPtr

    body : HasIO io => io DomNode
    body = map MkNode $ primIO $ prim__body ()

We create a ``DomNode`` type which holds an ``AnyPtr``. The ``prim__body`` function wraps a
lambda function with no parameters. In the Idris function ``body`` we pass an extra ``()`` parameter
and the we wrap the result in the ``DomNode`` type using the ``MkNode`` data constructor.

Primitive values originated in JavaScript
-----------------------------------------

As a countinuation of the previous example, the ``width`` attribute of a DOM element can be
retrieved via the FFI.

.. code-block:: idris

    %foreign "browser:lambda: n=>(n.width)"
    prim__width : AnyPtr -> PrimIO Bits32

    width : HasIO io => DomNode -> io Bits32
    width (MkNode p) = primIO $ prim__width p

Handling JavaScript events
--------------------------

.. code-block:: idris

    data DomEvent = MkEvent AnyPtr

    %foreign "browser:lambda: (event, callback, node) => node.addEventListener(event, x=>callback(x)())"
    prim__addEventListener : String -> (AnyPtr -> PrimIO ()) -> AnyPtr -> PrimIO ()

    addEventListener : HasIO io => String -> DomNode -> (DomEvent -> IO ()) -> io ()
    addEventListener event (MkNode n) callback =
      primIO $ prim__addEventListener event (\ptr => toPrim $ callback $ MkEvent ptr) n


In this example shows how to attach an event handler to a particular DOM element. Values of events
are also associated with ``AnyPtr`` on the Idris side. To seperate ``DomNode`` form ``DomEvent``
we create two different types. Also it demonstrates how a simple callback function defined in
Idris can be used on the JavaScript side.

Directives
----------

The javascript code generators accepts three different directives
about how compact and obfusacted the generated code should be.
The following examples show the code generated for the ``putStr``
function from the prelude for each of the three directives.
(``--cg node`` is used in the examples below, but the behavior is
the same when generating code to be run in browsers with ``--cg javascript``).

With ``idris2 --cg node --directive pretty`` (the default, if no directive is
given), a basic pretty printer is used to generate properly indented
javascript code.

.. code-block:: javascript

    function Prelude_IO_putStr($0, $1) {
     return $0.a2(undefined)($7 => Prelude_IO_prim__putStr($1, $7));
    }

With ``idris2 --cg node --directive compact``, every toplevel function
is declared on a single line, and unneeded spaces are removed:

.. code-block:: javascript

    function Prelude_IO_putStr($0,$1){return $0.a2(undefined)($7=>Prelude_IO_prim__putStr($1,$7));}

Finally, with ``idris2 --cg node --directive minimal``, toplevel function
names are (with a few exceptions like the ones from the static
preamble) obfuscated to reduce the size of the generated javascript
file:

.. code-block:: javascript

    function $R3a($0,$1){return $0.a2(undefined)($7=>$R3b($1,$7));}
