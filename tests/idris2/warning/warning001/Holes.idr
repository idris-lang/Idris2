test : List Nat -> List Nat
test [] = []
test (n :: ns) = ?n :: ns

replicate : (n : Nat) -> a -> List a
replicate Z a = []
replicate (S n) a = a :: replicate n a

testReplicate : test (replicate (1+n) k) === replicate (2+n) k
testReplicate = ?goal
