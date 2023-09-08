--- Data declarations ---

data (.ah) a = Ah (List a)

g : Int .ah -> Int
g (Ah xs) = sum xs

--- Records ---

record (.aah) a where
  constructor Aah
  unaah : List a

h : Num a => a.aah -> a
h = sum . unaah

--- Interfaces ---

interface (.defaultable) a where
  defa : a

(.defaultable) Int where
  defa = 0

f : Num a => a.defaultable => a -> a
f x = x + defa
