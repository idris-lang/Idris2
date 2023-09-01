%default total

-- We put it all in a failing block so as not to pollute the scope
-- The point is that because we have not specified `[search a]` when
-- defining `Wrap` then we cannot find the `Wrap` implementation in
-- the test.

failing "Can't find an implementation for Wrap ?ph Nat."

  record Wrap (phantom : Type) (a : Type) where
    constructor MkWrap
    unWrap : a

  %hint
  zero : Wrap Bool Nat
  zero = MkWrap 0

  getWrappedVal : Wrap ph a => a
  getWrappedVal @{w} = unWrap w

  test : Main.getWrappedVal === Z
  test = Refl

record Wrap (phantom : Type) (a : Type) where
  -- whereas this will give us the right behaviour
  [search a]
  constructor MkWrap
  unWrap : a

%hint
zero : Wrap Bool Nat
zero = MkWrap 0

getWrappedVal : Wrap ph a => a
getWrappedVal @{w} = unWrap w

test : Main.getWrappedVal === Z
test = Refl
