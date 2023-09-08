data Mu : (f : Type -> Type) -> Type where
  MkMu : f (Mu f) -> Mu f

%spec a, f, fun
fold : (fun : Functor f) => (f a -> a) -> Mu f -> a
fold alg (MkMu t) = alg (fold {a, f, fun} alg <$> t)

size : Mu List -> Nat
size = fold sum
