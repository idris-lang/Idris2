module Unsafe

%default total

record Exists (p : a -> Type) where
  constructor MkExists
  0 x : a
  prf : p x

%unsafe
lpo : (p : Nat -> Type) -> Either ((n : Nat) -> p n) (Exists $ \ n => Not (p n))

%unsafe
ext : {0 f, g : a -> b} -> ((x : a) -> f x === g x) -> f === g

example : (f : Nat -> Nat) -> Dec (f === const 0)
example f = case lpo (\ n => f n === 0) of
  Left prf => Yes (ext prf)
  Right (MkExists n prf) => No (\ eq => void (prf (cong ($ n) eq)))
