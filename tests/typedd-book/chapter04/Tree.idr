data Tree elt = Empty
               | Node (Tree elt) elt (Tree elt)

%name Tree tree, tree1

insert : Ord elt => elt -> Tree elt -> Tree elt
insert x Empty = Node Empty x Empty
insert x orig@(Node left val right)
    = case compare x val of
           LT => Node (insert x left) val right
           EQ => orig
           GT => Node left val (insert x right)
