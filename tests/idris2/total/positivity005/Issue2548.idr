%default total

data Recursive : (Lazy Type -> Type) -> Type where
  Recursing : t (delay (Recursive t)) -> Recursive t

F : Type
F = Recursive (\x => Not x)

notF : Not F
notF f@(Recursing nF) = nF f

f : F
f = Recursing notF

argh : Void
argh = notF f
