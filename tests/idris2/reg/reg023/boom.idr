import Data.Vect

%default total

infix 3 .<=.
(.<=.) : Int -> Int -> Bool
(.<=.) p q = case (p, q) of
  (0, _) => True
  _ => False

countGreater : (thr : Int) -> (ctx : Vect n Int) -> Nat
countGreater thr [] = Z
countGreater thr (x :: xs) with (x .<=. thr)
  countGreater thr (x :: xs) | True = countGreater thr xs
  countGreater thr (x :: xs) | False = S $ countGreater thr xs

-- map a variable from the old context to the erased context
-- where we erase all bindings less than or equal to the threshold
eraseVar : (thr : Int) -> (ctx : Vect n Int) -> Fin n -> Maybe (Fin (countGreater thr ctx))
eraseVar thr (x :: xs) j with (x .<=. thr)
  eraseVar thr (x :: xs) FZ | True = Nothing
  eraseVar thr (x :: xs) FZ | False = Just FZ
  eraseVar thr (x :: xs) (FS i) | True = FS <$> eraseVar thr xs i
  eraseVar thr (x :: xs) (FS i) | False = FS <$> eraseVar thr xs i

boom : Maybe (Fin 1)
boom = eraseVar 0 [0, 1] (FS FZ)
