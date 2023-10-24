data Bad = MkBad (Bad -> Int) Int
         | MkBad' Int

foo : Bad -> Int
foo (MkBad f i) = f (MkBad' i)
foo (MkBad' x) = x

foo2 : Bad -> Int
foo2 b = case b of
              MkBad f i => f (MkBad' i)
              MkBad' x => x

data T : Type -> Type where
     MkT : T (T a) -> T a

mutual
  data Bad1 = MkBad1 (Bad2 -> Int)
  data Bad2 = MkBad2 (Bad1 -> Int)

data T2 : Type -> Type where
     MkT2 : T a -> T2 a
