data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)

%name Tree tree, tree1

insert : Ord elem => elem -> Tree elem -> Tree elem
insert x Empty = Node Empty x Empty
insert x orig@(Node left val right)
    = case compare x val of
           LT => Node (insert x left) val right
           EQ => orig
           GT => Node left val (insert x right)
