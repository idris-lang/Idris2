***********************************
Javascript and Node Code Generators
***********************************

There two javascript code generators ``node`` and ``javascript``. There are two
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

    %foreign "node:lambdaRequire:fs:fp=>__require_fs.fstatSync(fp.fd, {bigint: true}).size"
    prim__fileSize : FilePtr -> PrimIO Int

``lambdaRequire`` also accepts a list of separated modules and assigns
them the name ``__require_<module name>``.

For completion below an example of a foreign available only with ``browser`` codegen:

.. code-block:: idris

    %foreign "browser:lambda:x=>{document.body.innerHTML = x}"
    prim__setBodyInnerHTML : String -> PrimIO ()


Full Example
------------

An interesting example is creating a foreign for the setTimeout function:

.. code-block:: idris

    %foreign "javascript:lambda:(callback, delay)=>setTimeout(callback, Number(delay))"
    prim__setTimeout : (PrimIO ()) -> Int -> PrimIO ()

    setTimeout : HasIO io => IO () -> Int -> io ()
    setTimeout callback delay = primIO $ prim__setTimeout (toPrim callback) delay

An important note here is that the codegen is using ``BigInt`` to represent
idris ``Int``, that's why we need to apply ``Number`` to the ``delay``.
