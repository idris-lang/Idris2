||| Test if :typeat correctly shows types within !(...)

n : List a -> List a
n xs = pure !xs

f : (a -> List b) -> a -> (b -> List c) -> List c
f g a j = j !(g a)
