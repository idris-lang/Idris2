Postfix projections
===================

.. role:: idris(code)
    :language: idris

Postfix projections are syntactic forms that represent postfix application,
such as ``person.name``. They were originally motivated by the need of dot syntax
to access fields of records, and generalised also for non-record use cases later.

The more advanced features require ``%language PostfixProjections``,
at least until it's clear whether they should be present in the language.

Lexical structure
-----------------

* ``.foo`` starting with lowercase ``f``, single identifier, and no space after dot,
  is a valid lexeme, which stands for postfix application of ``foo``

* ``Foo.Bar.baz`` with uppercase ``F`` and ``B`` is one lexeme: a namespaced
  identifier.

* ``Foo.Bar.baz.boo`` is two lexemes: ``Foo.Bar.baz`` and ``.boo``.

* ``foo.bar.baz`` starting with lowercase ``f`` is three lexemes: ``foo``,
  ``.bar``, ``.baz``

* ``.foo.bar.baz`` is three lexemes: ``.foo``, ``.bar``, ``.baz``

* ``foo . bar``, as well as ``foo. bar`` is three lexemes: ``foo``, ``.``, ``bar``,
  and represents function composition as usual

* Beware that ``True.not`` is lexed as "name ``not`` in module ``True``".
  If you want the postfix application of ``not`` to constructor ``True``,
  you have to write ``(True).not``.

* Spaces *before* dots are optional; spaces *after* dots are forbidden
  in postfix projections: ``foo. bar`` is parsed as function composition.

* All module names must start with an uppercase letter.

New syntax of ``simpleExpr``
----------------------------

Expressions binding tighter than application (``simpleExpr``),
such as variables or parenthesised expressions, have been renamed to ``simplerExpr``,
and an extra layer of postfix dot syntax has been inserted in ``simpleExpr``.

.. code-block:: idris

    postfixProj ::= .ident        -- identifiers need not be bracketed
                  | .(expr)       -- arbitrary expression in brackets

    simpleExpr ::= simplerExpr postfixProj+   -- postfix projection
                 | (postfixProj+ simpleExpr+) -- section of postfix projection
                 | simplerExpr                -- (parses as whatever it used to)

Desugaring rules
----------------

* Postfix projections:
  ``simpleExpr .proj1 .proj2 .proj3`` desugars to ``(proj3 (proj2 (proj1 simpleExpr))``

* Sections of postfix projections:
  ``(.proj1 .proj2 .proj3 arg1 arg2)`` desugars to ``(\x => x.proj1.proj2.proj3 arg1 arg2)``

Examples of desugaring:

* ``foo.bar`` desugars as ``bar foo``
* ``True.not`` is a single lexeme: qualified name
* ``(True).not`` desugars as ``not True``
* ``(True).(not . not)`` desugars as ``(not . not) True``
* ``(not True).(not . not)`` desugars as ``(not . not) (not True)``
* ``(checkFile fileName).runState initialState`` desugars as ``runState (checkFile fileName) initialState``
* ``(MkPoint 3 4).x`` desugars as ``x (MkPoint 3 4)``

Examples of desugaring sections:

* bare ``.foo`` is invalid syntax (e.g. in ``f $ .foo``)
* ``(.foo)`` desugars as ``(\x => x.foo)``, i.e. ``(\x => foo x)``
* ``(.foo.bar m n)`` desugars as ``(\x => bar (foo x) m n)``

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

    squared : Num a => a -> a
    squared x = x * x

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
      -- both print 4.2
      printLn $ Main.pt.x
      printLn $ (Main.pt).x

      -- the LHS can be an arbitrary expression
      -- prints 4.2
      printLn $ (MkPoint pt.y pt.x).y

      -- the RHS can be an arbitrary expression, too
      -- prints 17.64
      printLn $ (MkPoint pt.y pt.x).(squared . y)

      -- user-defined function
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
