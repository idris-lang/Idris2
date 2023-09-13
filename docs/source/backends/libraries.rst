***************
Libraries
***************

This pragma tells the backend what name to use for a given function.

.. code-block:: idris

    %nomangle
    foo : Int -> Int
    foo x = x + 1

On backends that support this feature, the function will be called ``foo``
rather than being mangled, with the namespace.

If the name you want to use isn't a valid idris identifier, you can use a different name
for the idris name and name that appears in the compiled code, e.g.

.. code-block:: idris

    %nomangle "$_baz"
    baz : Int
    baz = 42

You can also specify different names for different backends, in a similar way to %foreign

.. code-block:: idris

    %nomangle "refc:idr_add_one"
              "node:add_one"
    plusOne : Bits32 -> Bits32
    plusOne x = x + 1
