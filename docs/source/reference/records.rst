Dot syntax for records
======================

.. role:: idris(code)
    :language: idris

Long story short, ``.field`` is a postfix projection operator that binds
tighter than function application.

Lexical structure
-----------------

* ``.foo`` is a valid name, which stands for record fields (new ``Name``
  constructor ``RF "foo"``)

* ``Foo.bar.baz`` starting with uppercase ``F`` is one lexeme, a namespaced
  identifier: ``NSIdent ["baz", "bar", "Foo"]``

* ``foo.bar.baz`` starting with lowercase ``f`` is three lexemes: ``foo``,
  ``.bar``, ``.baz``

* ``.foo.bar.baz`` is three lexemes: ``.foo``, ``.bar``, ``.baz``

* If you want ``Constructor.field``, you have to write ``(Constructor).field``.

* All module names must start with an uppercase letter.

New syntax of ``simpleExpr``
----------------------------

Expressions binding tighter than application (``simpleExpr``), such as variables or parenthesised expressions, have been renamed to ``simplerExpr``, and an extra layer of syntax has been inserted.

.. code-block:: idris

    simpleExpr ::= (.field)+               -- parses as PRecordProjection
                 | simplerExpr (.field)+   -- parses as PRecordFieldAccess
                 | simplerExpr             -- (parses as whatever it used to)

* ``(.foo)`` is a name, so you can use it to e.g. define a function called
  ``.foo`` (see ``.squared`` below)

* ``(.foo.bar)`` is a parenthesised expression

Desugaring rules
----------------

* ``(.field1 .field2 .field3)`` desugars to ``(\x => .field3 (.field2 (.field1
  x)))``

* ``(simpleExpr .field1 .field2 .field3)`` desugars to ``((.field .field2
  .field3) simpleExpr)``

Record elaboration
------------------

* there is a new pragma ``%undotted_record_projections``, which is ``on`` by
  default

* for every field ``f`` of a record ``R``, we get:

  * projection ``f`` in namespace ``R`` (exactly like now), unless
    ``%undotted_record_projections`` is ``off``

  * projection ``.f`` in namespace ``R`` with the same definition

Example code
------------

.. code-block:: idris

    record Point where
      constructor MkPoint
      x : Double
      y : Double

This record creates two projections:
* ``.x : Point -> Double``
* ``.y : Point -> Double``

Because ``%undotted_record_projections`` are ``on`` by default, we also get:
* ``x : Point -> Double``
* ``y : Point -> Double``

To prevent cluttering the ordinary global name space with short identifiers, we can do this:

.. code-block:: idris

    %undotted_record_projections off

    record Rect where
      constructor MkRect
      topLeft : Point
      bottomRight : Point

For ``Rect``, we don't get the undotted projections:

.. code-block:: idris

    Main> :t topLeft
    (interactive):1:4--1:11:Undefined name topLeft
    Main> :t .topLeft
    \{rec:0} => .topLeft rec : ?_ -> Point

Let's define some constants:

.. code-block:: idris

    pt : Point
    pt = MkPoint 4.2 6.6

    rect : Rect
    rect =
      MkRect
        (MkPoint 1.1 2.5)
        (MkPoint 4.3 6.3)

User-defined projections work, too. (Should they?)

.. code-block:: idris

    (.squared) : Double -> Double
    (.squared) x = x * x

Finally, the examples:

.. code-block:: idris

    main : IO ()
    main = do
      -- desugars to (.x pt)
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

      -- .topLeft.y desugars to (\x => .y (.topLeft x))
      -- prints [2.5, 2.5]
      printLn $ map (.topLeft.y) [rect, rect]

      -- desugars to (.topLeft.x rect + .bottomRight.y rect)
      -- prints 7.4
      printLn $ rect.topLeft.x + rect.bottomRight.y

      -- qualified names work, too
      -- all these print 4.2
      printLn $ Main.Point.(.x) pt
      printLn $ Point.(.x) pt
      printLn $ (.x) pt
      printLn $ .x pt

      -- haskell-style projections work, too
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
