Dot syntax for records
======================

.. role:: idris(code)
    :language: idris

Long story short, ``.proj`` is a postfix projection operator that binds
tighter than function application.

Lexical structure
-----------------

* ``.foo`` is a valid lexeme, which stands for postfix application of ``foo``

* ``Foo.bar.baz`` starting with uppercase ``F`` is one lexeme, a namespaced
  identifier: ``DotSepIdent ["baz", "bar", "Foo"]``

* ``foo.bar.baz`` starting with lowercase ``f`` is three lexemes: ``foo``,
  ``.bar``, ``.baz``

* ``.foo.bar.baz`` is three lexemes: ``.foo``, ``.bar``, ``.baz``

* If you want ``Constructor.proj``, you have to write ``(Constructor).proj``.

* All module names must start with an uppercase letter.

New syntax of ``simpleExpr``
----------------------------

Expressions binding tighter than application (``simpleExpr``), such as variables or parenthesised expressions, have been renamed to ``simplerExpr``, and an extra layer of syntax has been inserted.

.. code-block:: idris

    postfixProj ::= .identifier
                  | .(expression)

    simpleExpr ::= (postfixProj+ simpleExpr+) -- parses as PPostfixProjPartial
                 | simplerExpr postfixProj+   -- parses as PPostfixProj
                 | simplerExpr                -- (parses as whatever it used to)

* ``(.foo.bar arg1 arg2)`` is a section of ``x.foo.bar arg1 arg2``

Desugaring rules
----------------

* ``(.proj1 .proj2 .proj3 arg1 arg2)`` desugars to ``(\x => x.proj1.proj2.proj3 arg1 arg2)``

* ``simpleExpr .proj1 .proj2 .proj3`` desugars to
  ``(proj3 (proj2 (proj1 simpleExpr))``

Example code
------------

.. code-block:: idris

    record Point where
      constructor MkPoint
      x : Double
      y : Double

This record creates two projections:
* ``x : Point -> Double``
* ``y : Point -> Double``

We add another record:

.. code-block:: idris

    record Rect where
      constructor MkRect
      topLeft : Point
      bottomRight : Point

Let's define some constants:

.. code-block:: idris

    pt : Point
    pt = MkPoint 4.2 6.6

    rect : Rect
    rect =
      MkRect
        (MkPoint 1.1 2.5)
        (MkPoint 4.3 6.3)

Finally, some examples:

.. code-block:: idris

    main : IO ()
    main = do
      -- desugars to (x pt)
      -- prints 4.2
      printLn $ pt.x

      -- prints 4.2, too
      -- maybe we want to make this a parse error?
      printLn $ pt .x

      -- prints 10.8
      printLn $ pt.x + pt.y

      -- works fine with namespacing
      -- prints 4.2
      printLn $ (Main.pt).x

      -- the LHS can be an arbitrary expression
      -- prints 4.2
      printLn $ (MkPoint pt.y pt.x).y

      -- user-defined projection
      -- prints 17.64
      printLn $ pt.x.squared

      -- prints [1.0, 3.0]
      printLn $ map (.x) [MkPoint 1 2, MkPoint 3 4]

      -- .topLeft.y desugars to (\x => y (topLeft x))
      -- prints [2.5, 2.5]
      printLn $ map (.topLeft.y) [rect, rect]

      -- desugars to (.topLeft.x rect + .bottomRight.y rect)
      -- prints 7.4
      printLn $ rect.topLeft.x + rect.bottomRight.y

      -- complex projections
      -- prints 7.4
      printLn $ rect.(x . topLeft) + rect.(y . bottomRight)

      -- haskell-style projections
      printLn $ Main.Point.x pt
      printLn $ Point.x pt
      printLn $ (x) pt
      printLn $ x pt

      -- record update syntax uses dots now
      -- prints 3.0
      printLn $ (record { topLeft.x = 3 } rect).topLeft.x

      -- but for compatibility, we support the old syntax, too
      printLn $ (record { topLeft->x = 3 } rect).topLeft.x

      -- prints 2.1
      printLn $ (record { topLeft.x $= (+1) } rect).topLeft.x
      printLn $ (record { topLeft->x $= (+1) } rect).topLeft.x

Parses but does not typecheck:

.. code-block:: idris

  -- parses as: map.x [MkPoint 1 2, MkPoint 3 4]
  -- maybe we should disallow spaces before dots?
  --
  printLn $ map .x [MkPoint 1 2, MkPoint 3 4]
