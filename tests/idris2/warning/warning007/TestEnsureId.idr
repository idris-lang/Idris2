module TestEnsureId

%ensure_identity
myId : a -> a
myId x = x

%ensure_identity
myId' : a -> b -> c -> b
myId' x y z = y

%ensure_identity
notId : Nat -> Bool
notId 0 = False
notId 1 = True
notId (S n) = notId n

