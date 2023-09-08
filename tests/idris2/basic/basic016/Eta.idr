data Test : Type where
     MkTest : Integer -> Integer -> Test

etaGood1 : MkTest = (\x => \y => MkTest ? ?)
etaGood1 = Refl

etaGood2: (MkTest 1) = (\x => MkTest ? x)
etaGood2 = Refl

etaGood3: (f : a -> b) -> f = (\x => f x)
etaGood3 f = Refl

etaBad : MkTest = (\x : Nat => \y => MkTest ? ?)
etaBad = Refl
