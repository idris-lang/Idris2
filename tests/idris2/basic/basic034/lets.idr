data A : Type where
  The : Type -> A

U : A -> Type
U (The x) = x

works : (a : A) -> (H : U a) -> (let q = H in Nat)
works a h = 0

fails : (a : A) -> (H : U a) -> (let q : U a = H in Nat)
fails a h = 0

dolet : Maybe Int -> Maybe Int -> Maybe Int
dolet x y
    = do let Just x' : Maybe Int = x
             | Nothing => Nothing
         y' <- y
         pure (x' + y')

dolet2 : Maybe Int -> Maybe Int -> Maybe Int
dolet2 x y
    = do let Just x' : Maybe String = x
             | Nothing => Nothing
         y' <- y
         pure (x' + y')
