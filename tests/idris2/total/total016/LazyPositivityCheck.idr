%default total

failing "Oops is not total, not strictly positive"

  data Oops : Type where
    MkOops : (Lazy Oops -> Void) -> Oops

  oops : Not (Lazy Oops)
  oops a@(MkOops b) = b a

  boom : Void
  boom = oops (MkOops oops)

failing "Oops is not total, not strictly positive"

  data Oops : Type where
    MkOops : Lazy (Oops -> Void) -> Oops

  oops : Not Oops
  oops a@(MkOops b) = b a

  boom : Void
  boom = oops (MkOops oops)
