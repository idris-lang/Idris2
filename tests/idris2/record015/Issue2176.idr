
--------------------------------------------------------------------------------
-- data (this worked before)

fd : Int
fd = 5 where
  data X : Type where
    MkX : Int -> X

gd : Int
gd = 5 where
  data X : Type where
    MkX : Int -> X

--------------------------------------------------------------------------------
-- record without fields or constructor

fr0 : Int
fr0 = 5 where
  record X where

gr0 : Int
gr0 = 5 where
  record X where

--------------------------------------------------------------------------------
-- record without fields but with constructor

fr1 : Int
fr1 = 5 where
  record X where
    constructor MkX

gr1 : Int
gr1 = 5 where
  record X where
    constructor MkX

--------------------------------------------------------------------------------
-- record with a field and constructor

fr2 : Int
fr2 = 5 where
  record X where
    constructor MkX
    field1 : Int

gr2 : Int
gr2 = 5 where
  record X where
    constructor MkX
    field1 : Int

--------------------------------------------------------------------------------
-- record with two fields and constructor

fr3 : Int
fr3 = 5 where
  record X where
    constructor MkX
    field1 : Int
    field2 : Bool

gr3 : Int
gr3 = 5 where
  record X where
    constructor MkX
    field1 : Char
    field2 : String

--------------------------------------------------------------------------------
-- record with parameter

fr4 : Int
fr4 = 5 where
  record X (a : Type) where
    constructor MkX
    field1 : Int
    field2 : a

gr4 : Int
gr4 = 5 where
  record X (a : Type) where
    constructor MkX
    field1 : a
    field2 : String

--------------------------------------------------------------------------------
-- complex example

fr5 : List Int
fr5 = fun k where

  k : Int
  k = 5

  record X (a : Type) where
    constructor MkX
    xfield1 : Int
    xfield2 : (X a -> Int)
    xfield3 : a

  rec : X Int
  rec = MkX (k+1) (const (k+2)) 3

  fun : Int -> List Int
  fun n = n :: rec.xfield1 :: rec.xfield2 rec :: rec.xfield3 :: []

gr5 : List Int
gr5 = fun k where

  k : Int
  k = 6

  record X (a : Type) where
    constructor MkX
    xfield1 : Int
    xfield2 : (X a -> Int)
    xfield3 : a

  rec : X Int
  rec = MkX (k+3) (const (k+4)) 5

  fun : Int -> List Int
  fun n = n :: rec.xfield1 :: rec.xfield2 rec :: rec.xfield3 :: []

--------------------------------------------------------------------------------

main : IO ()
main = do
  printLn $ fr5
  printLn $ gr5

--------------------------------------------------------------------------------
