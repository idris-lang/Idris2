import Data.Vect
record Foo (th : Vect n a) where
  nIsZero     : n === 0
  vectIsEmpty : (th ===)
                 $ replace {p = \ n => Vect n a} (sym nIsZero)
                 $ Nil

