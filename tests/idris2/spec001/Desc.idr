module Desc

%default total

data Desc = Stop | Prod Desc Desc | Sum Desc Desc | Rec

%name Desc d, e

Meaning : Desc -> Type -> Type
Meaning Stop x = ()
Meaning (Prod d e) x = (Meaning d x, Meaning e x)
Meaning (Sum d e) x = Either (Meaning d x) (Meaning e x)
Meaning Rec x = x

%spec d
fmap : (d : Desc) -> (f : a -> b) -> Meaning d a -> Meaning d b
fmap Stop f = id
fmap (Prod d e) f = bimap (fmap d f) (fmap e f)
fmap (Sum d e) f = bimap (fmap d f) (fmap e f)
fmap Rec f = f

data Mu : Desc -> Type where
  MkMu : Meaning d (assert_total (Mu d)) -> Mu d

%spec d
fold : {d : Desc} -> (Meaning d a -> a) -> Mu d -> a
fold alg (MkMu t) = alg (fmap d (assert_total (fold alg)) t)

Tree : Desc
Tree = Sum Stop (Prod Rec Rec)

size : Mu Tree -> Nat
size = fold $ \case
  Left v => 0
  Right v => 1 + uncurry (+) v

t : Mu Tree
t = MkMu (Left ())

main : IO ()
main = printLn (size t)
