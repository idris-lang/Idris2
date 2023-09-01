module Test

data Dummy : (lbl : Type) -> (st : List lbl) -> Type -> Type where
  MkDummy : a -> Dummy b st a


public export
interface IxPure (f : (lbl : Type) -> (st : List lbl) -> Type -> Type)
          where
  ixPure : a -> f lbl st a

IxPure Dummy where
  ixPure = MkDummy

pure12 : Dummy String xs Nat
pure12 = ixPure Z
