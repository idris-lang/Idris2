data List' a = Nil | Cons a (List' a)

-- Generated with `:gd 4 mapList'`
mapList' : ((1 x : a) -> b) -> (1 xs : List' a) -> List' b
mapList' f [] = []
mapList' f (Cons x y) = Cons (f x) (mapList' f y)

data Tree1 a = Nil1 | Node1 a (Tree1 a) (Tree1 a)

mapTree1 : ((1 x : a) -> b) -> (1 t : Tree1 a) -> Tree1 b

data Tree2 a = Nil2 | Node2 a (List' (Tree2 a))

-- TODO: Fix not entirly appropriate definition (nulls list of Node2)
mapTree2 : ((1 x : a) -> b) -> (1 t : Tree2 a) -> Tree2 b
