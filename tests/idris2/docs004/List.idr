module List

data List a = Nil | (::) a (List a)

infixr 5 ::
infixr 5 ++

interface Monoid ty where
  neutral : ty
  (++) : ty -> ty -> ty

Monoid (List a) where
  neutral = []

  xs ++ ys = case xs of
    [] => ys
    (x :: xs) => let ih = xs ++ ys in x :: ih
