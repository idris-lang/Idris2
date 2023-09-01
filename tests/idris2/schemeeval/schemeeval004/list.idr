import Data.List

mkList : a -> Nat -> List a
mkList x Z = ?help
mkList x (S k) = x :: mkList x k

-- For a performance test: make sure we evaluate the full list, and get
-- a result that we don't have to work hard to render
isEven : Nat -> Bool
isEven Z = True
isEven (S k) = not (isEven k)
