%default partial

data Foo : Int -> Type where
     FZero : Foo 0
     FPlus : (x : Int) -> (y : Int) -> Foo (x + y)

tfoo : (x : Int) -> Foo x -> Int
tfoo 0 FZero = ?bar
tfoo (x + y) (FPlus x y) = ?baz

foo : (x : Int) -> Foo x

wfoo : (x : Int) -> Int
wfoo x with (foo x)
  wfoo 0 | FZero = ?wfoo_rhs_1
  wfoo (y + z) | (FPlus y z) = ?wfoo_rhs_2

wbar : (x : Int) -> Int
wbar x with (foo x)
  wbar 0 | FZero = ?wbar_rhs_1
  wbar (1 + z) | (FPlus 1 z) = ?wbar_rhs_2

wbar1 : (x : Int) -> Int
wbar1 x with (foo x)
  wbar1 0 | FZero = ?wbar1_rhs_1
  wbar1 (1 + z) | (FPlus 1 z) = ?wbar1_rhs_2
  wbar1 (y + z) | (FPlus y z) = ?wbar1_rhs_3
