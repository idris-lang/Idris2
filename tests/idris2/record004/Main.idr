module Main

record Point where
  constructor MkPoint
  x : Double
  y : Double

-- a record creates two projections:
--
-- .x : Point -> Double
-- .y : Point -> Double
--
-- because %undotted_record_projections are on by default, we also get:
--
-- x : Point -> Double
-- y : Point -> Double

-- to prevent cluttering the ordinary name space with short identifiers
%undotted_record_projections off

record Rect where
  constructor MkRect
  topLeft : Point
  bottomRight : Point

-- .topLeft : Rect -> Point
-- .bottomRight : Rect -> Point
--
-- For Rect, we don't get the undotted projections:
--
-- Main> :t topLeft
-- (interactive):1:4--1:11:Undefined name topLeft
-- Main> :t .topLeft
-- \{rec:0} => .topLeft rec : ?_ -> Point


pt : Point
pt = MkPoint 4.2 6.6

rect : Rect
rect =
  MkRect
    (MkPoint 1.1 2.5)
    (MkPoint 4.3 6.3)

-- New lexical structure:
--
-- Foo.bar.baz with uppercase F is one lexeme: NSIdent ["baz", "bar", "Foo"]
-- foo.bar.baz with lowercase f is three lexemes: foo, .bar, .baz
-- .foo.bar.baz is three lexemes: .foo, .bar, .baz
--
-- If you want Constructor.field, you have to write (Constructor).field.
--
-- New syntax of simpleExpr:
--
-- Expressions binding tighter than application (simpleExpr),
-- such as variables or parenthesised expressions,
-- have been renamed to simplerExpr,
-- and an extra layer of syntax has been inserted.
-- 
--   simpleExpr ::= (.field)+               -- parses as PRecordProjection
--                | simplerExpr (.field)+   -- parses as PRecordFieldAccess
--                | simplerExpr             -- (parses as whatever it used to)
--
-- (.foo) is a name, so you can use it to e.g. define a function called .foo (see .squared below)
-- (.foo.bar) is a parenthesised expression
--
-- New desugaring rules
--
-- (.field1 .field2 .field3) desugars to (\x => .field3 (.field2 (.field1 x)))
-- (simpleExpr .field1 .field2 .field3) desugars to ((.field .field2 .field3) simpleExpr).
--
-- There are more details such as namespacing; see below.

-- user-defined projections work, too (should they?)
(.squared) : Double -> Double
(.squared) x = x * x
