import OopsDef

%default total

failing "Oops is not total, not strictly positive"

  data OopsDef.Oops : Type where
    MkFix : Not Oops -> Oops
