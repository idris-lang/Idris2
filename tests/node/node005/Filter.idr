data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

Show a => Show (Vect n a) where
  show xs = "[" ++ showV xs ++ "]"
    where
      showV : forall n . Vect n a -> String
      showV [] = ""
      showV [x] = show x
      showV (x :: xs) = show x ++ ", " ++ showV xs

filter : (a -> Bool) -> Vect n a -> (p ** Vect p a)
filter pred [] = (_ ** [])
filter pred (x :: xs)
    = let (n ** xs') = filter pred xs in
          if pred x
             then (_ ** x :: xs')
             else (_ ** xs')

test : (x ** Vect x Nat)
test = (_ ** [1,2])

foo : String
foo = show test

even : Nat -> Bool
even Z = True
even (S k) = not (even k)
