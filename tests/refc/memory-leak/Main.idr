module Main

data BTree a = Leaf
             | Node (BTree a) a (BTree a)

insert : Ord a => a -> BTree a -> BTree a
insert x Leaf = Node Leaf x Leaf
insert x (Node l v r) = if (x < v) then (Node (insert x l) v r)
                                   else (Node l v (insert x r))

treePrint : Show a => BTree a -> IO ()
treePrint (Node l v r) = do
  treePrint l
  printLn v
  treePrint r
treePrint Leaf = pure ()

main : IO ()
main = do
  let tree1 = insert 4 $ insert 2 Leaf
  let tree2 = insert 5 $ insert 3 tree1
  treePrint tree2
  treePrint tree1
