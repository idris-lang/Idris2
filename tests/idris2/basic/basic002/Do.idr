data Maybe a = Nothing
             | Just a

infixl 1 >>=

(>>=) : Maybe a -> (a -> Maybe b) -> Maybe b
(>>=) Nothing k = Nothing
(>>=) (Just x) k = k x

data Nat : Type where
   Z : Nat
   S : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Z     y = y
plus (S k) y = S (plus k y)

maybeAdd' : Maybe Nat -> Maybe Nat -> Maybe Nat
maybeAdd' x y
    = x >>= \x' =>
      y >>= \y' =>
      Just (plus x' y')

maybeAdd : Maybe Nat -> Maybe Nat -> Maybe Nat
maybeAdd x y
    = do x' <- x
         y' <- y
         Just (plus x' y')

data Either : Type -> Type -> Type where
     Left : a -> Either a b
     Right : b -> Either a b

mEmbed : Maybe a -> Maybe (Either String a)
mEmbed Nothing = Just (Left "FAIL")
mEmbed (Just x) = Just (Right x)

mPatBind : Maybe Nat -> Maybe Nat -> Maybe Nat
mPatBind x y
    = do Right res <- mEmbed (maybeAdd x y)
            | Left err => Just Z
         Just res

mLetBind : Maybe Nat -> Maybe Nat -> Maybe Nat
mLetBind x y
    = do let Just res = maybeAdd x y
                  | Nothing => Just Z
         Just res
