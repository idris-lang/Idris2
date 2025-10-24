record Record1 where
  f : Type -> {_ : Type} -> Type

record Record2 where
  f : {x : Type} -> Type

record Record3 where
  f : (x : Type) => Type

record Record4 where
  f : Type => Type => Type

record Record5 where
  f : {X : Type} -> Type

record Record6 where
  f : (X : Type) => Type

record Record7 where
  f : {_ : Type} -> Type

record Record8 where
  f : {x : Type} -> {x : Int} -> {_ : String} -> (x : Double) => {x : Integer} -> Type

record Record9 where
  f : (_ : Type) => () -> () -> ()

record Record10 where
  f : {default Int _ : Type} -> () -> () -> ()
