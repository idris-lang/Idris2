data BSTree : Type -> Type where
     Empty : Ord elt => BSTree elt
     Node : Ord elt => (left : BSTree elt) -> (val : elt) ->
                        (right : BSTree elt) -> BSTree elt

insert : elt -> BSTree elt -> BSTree elt
insert x Empty = Node Empty x Empty
insert x orig@(Node left val right)
      = case compare x val of
             LT => Node (insert x left) val right
             EQ => orig
             GT => Node left val (insert x right)
