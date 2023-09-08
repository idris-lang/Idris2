%default total

--------------------------------------------------------
-- Shrunk

data D : List (List a) -> Type where
  C1 : D [ts]
  C2 : D [ts]

f : D [[Maybe a]] -> Nat
f C1 = 0
f C2 = 0

--------------------------------------------------------
-- Original bug report

data NP : (ts : List Type) -> Type where
  Nil  : NP []
  (::) : (v : t) -> (vs : NP ts) -> NP (t :: ts)

data NS : (kss : List $ List Type) -> Type where
  Z : (vs : NP ts) -> NS (ts :: tss)
  S : NS tss -> NS (ts :: tss)

Uninhabited (NS []) where
  uninhabited (Z _) impossible
  uninhabited (S _) impossible

data Funny : (a : Type) -> (f : Type -> Type) -> Type where
  A : List a -> f a -> Funny a f
  B : Funny a f

decode : NS [[List a, f a], []] -> Funny a f
decode (Z [a,b])  = A a b
decode (S (Z [])) = B
