data Nat : Type where
     Z : Nat
     S : (1 k : Nat) -> Nat

data Bool : Type where
     False : Bool
     True : Bool

data Thing : Bool -> Type where
     TF : Thing False
     TT : Thing True

data Maybe : Type -> Type where
     Nothing : {a : Type} -> Maybe a
     Just : {a : Type} -> a -> Maybe a

ok : (0 b : Bool) -> Thing b -> Bool
ok False TF = True
ok True TT = False

id : {a : Type} -> (1 x : a) -> a
id x = x

test : (1 x : Nat) -> Nat
test x = id x

data Pair : Type -> Type -> Type where
     MkPair : (1 x : a) -> (0 y : b) -> Pair a b

fst : (1 p : Pair a b) -> a
fst (MkPair x y) = x

wibble : (1 p : Pair a b) -> a
wibble {a=a} (MkPair x y)
    = let test : (1 y : a) -> a
          test y = y in
      test x

plus : (1 x : Nat) -> (1 y : Nat) -> Nat
plus Z y = y
plus (S k) y = S (plus k y)

holetest1 : (1 x : Nat) -> (1 y : Nat) -> Nat
holetest1 x y = plus ?this y

holetest2 : (1 x : Nat) -> (1 y : Nat) -> Nat
holetest2 x y = plus x ?that

