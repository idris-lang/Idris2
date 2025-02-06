interface Ok1 where
  fOk : Type -> Type -> Type

interface Fail1 where
  fFail : Type -> {_ : Type} -> Type

interface Ok2 where
  gOk : (x : Type) -> Type

interface Fail2 where
  gFail : {x : Type} -> Type
