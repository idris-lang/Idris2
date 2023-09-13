interface IsEven a where
    isEven : a -> Bool

interface IsOdd b where
    isOdd : b -> Bool

implementation IsOdd Nat

implementation IsEven Nat where
    isEven 0 = True
    isEven (S k) = not $ isOdd k

implementation Show Nat => IsOdd Nat where
    isOdd 0 = True
    isOdd (S k) = not $ isEven k

