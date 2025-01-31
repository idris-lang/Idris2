%default total

data Negation : Type -> Type

failing "Absurd is not total, not strictly positive"

  data Absurd : Type -> Type where
    MkAbsurd : Negation (Absurd a) -> Absurd a

