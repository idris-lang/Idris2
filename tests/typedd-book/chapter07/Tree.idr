data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)

Eq elem => Eq (Tree elem) where
    (==) Empty Empty = True
    (==) (Node left e right) (Node left' e' right')
          = left == left' && e == e' && right == right'
    (==) _ _ = False

Functor Tree where
    map f Empty = Empty
    map f (Node left e right)
        = Node (map f left)
               (f e)
               (map f right)

Foldable Tree where
  foldr f acc Empty = acc
  foldr f acc (Node left e right) = let leftfold = foldr f acc left
                                        rightfold = foldr f leftfold right in
                                        f e rightfold
