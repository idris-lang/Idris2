module Main

record Point where
  constructor MkPoint
  x : Double
  y : Double

-- a record creates two projections:
-- x : Point -> Double
-- y : Point -> Double

record Rect where
  constructor MkRect
  topLeft : Point
  bottomRight : Point

pt : Point
pt = MkPoint 4.2 6.6

rect : Rect
rect =
  MkRect
    (MkPoint 1.1 2.5)
    (MkPoint 4.3 6.3)

-- Foo.bar.baz with uppercase F is one lexeme: DotSepIdent ["baz", "bar", "Foo"]
-- foo.bar.baz with lowercase f is three lexemes: foo, .bar, .baz
-- .foo.bar.baz is three lexemes: .foo, .bar, .baz
--
-- If you want Constructor.field, you have to write (Constructor).field.

add : Num a => a -> a -> a
add x y = x + y

oopFoldl : List a -> b -> (b -> a -> b) -> b
oopFoldl xs z f = foldl f z xs

bad : Double
bad = 
  rect.x.topLeft        -- should not throw errors
  + rect.(x . topLeft)  -- disallowed without %language PostfixProjections

bad2 : Double
bad2 = (.oopFoldl 0 (+))  -- disallowed without %language PostfixProjections

%language PostfixProjections
-- from now on, we can use complex projections
