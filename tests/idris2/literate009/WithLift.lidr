> data Elem : a -> List a -> Type where
>      Here : Elem x (x :: xs)
>      There : Elem x xs -> Elem x (y :: xs)

> interface DecEq a where
>   decEq : (x : a) -> (y : a) -> Dec (x = y)

> zeroNotSucc : Z = (S k) -> Void
> zeroNotSucc Refl impossible

> recNotEq : (k = j -> Void) -> (S k) = (S j) -> Void

> DecEq Nat where
>   decEq Z Z = Yes Refl
>   decEq Z (S k) = No zeroNotSucc
>   decEq (S k) Z = No ?succNotZero
>   decEq (S k) (S j) with (decEq k j)
>     decEq (S j) (S j) | (Yes Refl) = Yes Refl
>     decEq (S k) (S j) | (No contra) = No ?recNotEqLift

> isElem : DecEq a => (x : a) -> (xs : List a) -> Maybe (Elem x xs)
> isElem x [] = Nothing
> isElem x (y :: xs) with (decEq x y)
>   isElem y (y :: xs) | (Yes Refl) = Just Here
>   isElem x (y :: xs) | (No contra) with (isElem x xs)
>     isElem x (y :: xs) | (No contra) | Nothing = Nothing
>     isElem x (y :: xs) | (No contra) | (Just z) = Just (There z)
