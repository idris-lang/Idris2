||| The content of this module is based on the paper
||| A Completely Unique Account of Enumeration
||| by Cas van der Rest, and Wouter Swierstra
||| https://doi.org/10.1145/3547636

module Data.Description.Indexed

%default total

public export
data IDesc : (p : Type -> Type) -> (i : Type) -> Type where
  Zero : IDesc p i
  One : IDesc p i
  Id : i -> IDesc p i
  (*) : (d1, d2 : IDesc p i) -> IDesc p i
  (+) : (d1, d2 : IDesc p i) -> IDesc p i
  Sig : (s : Type) -> p s -> (s -> IDesc p i) -> IDesc p i

public export
Elem : IDesc p i -> (i -> Type) -> Type
Elem Zero x = Void
Elem One x = ()
Elem (Id i) x = x i
Elem (d1 * d2) x = (Elem d1 x, Elem d2 x)
Elem (d1 + d2) x = Either (Elem d1 x) (Elem d2 x)
Elem (Sig s prop d) x = (v : s ** Elem (d v) x)

public export
data Fix : (i -> IDesc p i) -> i -> Type where
  MkFix : assert_total (Elem (d i) (Fix d)) -> Fix d i

namespace Example

  VecD : Type -> Nat -> IDesc (const ()) Nat
  VecD a 0 = One
  VecD a (S n) = Sig a () (const (Id n))

export
map : (d : IDesc p i) -> ((v : i) -> x v -> y v) -> Elem d x -> Elem d y
map Zero f v = v
map One f v = v
map (Id i) f v = f i v
map (d1 * d2) f (v, w) = (map d1 f v, map d2 f w)
map (d1 + d2) f (Left v) = Left (map d1 f v)
map (d1 + d2) f (Right v) = Right (map d2 f v)
map (Sig s _ d) f (x ** v) = (x ** map (d x) f v)

export
ifold : {d : i -> IDesc p i} ->
        ((v : i) -> Elem (d v) x -> x v) ->
        {v : i} -> Fix d v -> x v
ifold alg (MkFix t) = alg v (assert_total $ Indexed.map (d v) (\ _ => ifold alg) t)
