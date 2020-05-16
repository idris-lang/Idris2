module Algebra.Preorder

||| Preorder defines a binary relation using the `<=` operator
public export
interface Preorder a where
  (<=) : a -> a -> Bool
  preorderRefl : {x : a} -> x <= x = True
  preorderTrans : {x, y, z : a} -> x <= y = True -> y <= z = True -> x <= z = True

||| Least Upper Bound, replace max using only Preorder
export
lub : Preorder a => a -> a -> a
lub x y = if x <= y then y else x

||| Greatest Lower Bound, replaces min using only Preorder
export
glb : Preorder a => a -> a -> a
glb x y = if x <= y then x else y

||| Strict less-than using the relation from a preorder
public export
(<) : (Preorder a, Eq a) => a -> a -> Bool
(<) x y = x <= y && x /= y

||| The greatest bound of a bounded lattice, we only need to know about preorders however
public export
interface Preorder a => Top a where
  top : a
  topAbs : {x : a} -> x <= top = True
