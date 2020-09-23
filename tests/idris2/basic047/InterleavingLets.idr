data Tag = MkTag

data Elem :  a -> List a ->Type where
  Z : Elem a (a :: as)
  S : Elem a as -> Elem a (b :: as)

toNat : Elem as a -> Nat
toNat Z = 0
toNat (S n) = 1 + toNat n

Show (Elem as a) where
  show = show . toNat

data Subset : List a -> List a -> Type where
  Nil  : Subset [] bs
  (::) : Elem a bs -> Subset as bs -> Subset (a :: as) bs

toList : Subset as bs -> List Nat
toList [] = []
toList (n :: ns) = toNat n :: toList ns

Show (Subset as bs) where
  show = show . toList

search : {auto prf : a} -> a
search = prf

test : String
test =
  let x : Tag := MkTag
      y : Tag := MkTag

      as : List Tag
      as = [y,x]

      bs : List Tag
      bs = [x,y,y]

      prf : Subset as bs
      prf = search

      prf' : Subset as bs := search

      eq : prf === [S (S Z), Z] := Refl

--      eq' : prf' === [S (S Z), Z] := Refl
-- ^ does not work because  prf' is opaque

  in show prf


reverse : List a -> List a
reverse xs =
  let revOnto : List a -> List a -> List a
      revOnto acc [] = acc
      revOnto acc (x :: xs) = revOnto (x :: acc) xs

      rev := revOnto []

      result := rev xs

  in result
