module InlineCase

data BTree : Type where
  Leaf : BTree
  Node : BTree -> Nat -> BTree -> BTree

product : BTree -> Nat
product Leaf = 1
product (Node l n r)
  = %inline case n of
      Z => Z
      _ => %inline case product l of
        Z => Z
        pl => %inline case product r of
          Z => Z
          pr => pl * n * pr

myfun : Nat -> Nat
myfun Z = Z
myfun n = S $ case n of
  Z => Z
  S n => myfun n

main : IO ()
main = do
  l <- getLine
  print (product $ Node Leaf (length l) Leaf)
