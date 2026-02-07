tabulate : (Nat -> a) -> Stream a
tabulate f = f 0 :: tabulate (f . S)

index : Stream a -> Nat -> a
index (x :: _)  Z     = x
index (_ :: xs) (S n) = index xs n

lemma : (f : Nat -> Nat)
        -> (k : Nat)
        -> index (tabulate (f . S)) k = index (tabulate (\m => f (S m))) k
lemma f k = Refl
