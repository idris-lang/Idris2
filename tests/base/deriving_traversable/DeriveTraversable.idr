module DeriveTraversable

import Deriving.Functor
import Deriving.Foldable
import Deriving.Traversable

%language ElabReflection
%default covering

%logging "derive.traversable.clauses" 1
%logging "derive.traversable.assumption" 10

listT : Traversable List
listT = %runElab derive

maybeT : Traversable Maybe
maybeT = %runElab derive

eitherT : Traversable (Either err)
eitherT = %runElab derive

-- If we didn't have a `Foldable (Pair a)` instance and the tactics
-- unfortunately builds
-- pairT = let traversePair = (...) in
--         MkTraversable @{pairT .foldable} traversePair
-- because the `pairT` name is a %hint.
--
-- TODO: find a way to program defensively against this!
--failing "pairT is not total"
--
--  %hint total
--  pairT : Traversable (Pair a)
--  pairT = %runElab derive

total
pairM : Foldable (Pair a)
pairM = %runElab derive

total
pairT : Traversable (Pair a)
pairT = %runElab derive

namespace Constant

  record Constant (a, b : Type) where
    constructor MkConstant
    runConstant : a

  %hint
  constantF : Functor (Constant a)
  constantF = %runElab derive

  %hint
  constantM : Foldable (Constant a)
  constantM = %runElab derive

  constantT : Traversable (Constant a)
  constantT = %runElab derive

namespace Vect

  public export
  data Vect : Nat -> Type -> Type where
    Nil : Vect Z a
    (::) : a -> Vect n a -> Vect (S n) a

  %hint total
  vectF : Functor (Vect n)
  vectF = %runElab derive

  %hint total
  vectM : Foldable (Vect n)
  vectM = %runElab derive

  export %hint
  total
  vectT : Traversable (Vect n)
  vectT = %runElab derive


namespace Matrix

  record Matrix m n a where
    constructor MkMatrix
    runMatrix : Vect m (Vect n a)

  %hint total
  matrixF : Functor (Matrix m n)
  matrixF = %runElab derive

  %hint total
  matrixM : Foldable (Matrix m n)
  matrixM = %runElab derive

  total
  matrix : Traversable (Matrix m n)
  matrix = %runElab derive

namespace Tm

  data Op : Nat -> Type where
    Neg : Op 1
    Add : Op 2

  data Tm : Type -> Type where
    Var : a -> Tm a
    Call : Op n -> Vect n (Tm a) -> Tm a
    Lam : Tm (Maybe a) -> Tm a

  %hint total
  tmF : Functor Tm
  tmF = %runElab derive

  %hint total
  tmM : Foldable Tm
  tmM = %runElab derive

  total
  tm : Traversable Tm
  tm = %runElab derive

namespace Forest

  data Tree : Type -> Type
  data Forest : Type -> Type

  data Tree : Type -> Type where
    Leaf : a -> Tree a
    Node : Forest a -> Tree a

  data Forest : Type -> Type where
    Empty : Forest a
    Plant : Tree a -> Forest a -> Forest a

  %hint total treeF : Functor Tree
  %hint total forestF : Functor Forest

  treeF = %runElab derive {mutualWith = [`{Forest}]}
  forestF = %runElab derive {mutualWith = [`{Tree}]}

  %hint total treeM : Foldable Tree
  %hint total forestM : Foldable Forest

  treeM = %runElab derive {mutualWith = [`{Forest}]}
  forestM = %runElab derive {mutualWith = [`{Tree}]}

  %hint total treeT : Traversable Tree
  %hint total forestT : Traversable Forest

  treeT = %runElab derive {mutualWith = [`{Forest}]}
  forestT = %runElab derive {mutualWith = [`{Tree}]}

namespace List1

  %hide List1

  data List1 : Type -> Type where
    MkList1 : (a, Maybe (List1 a)) -> List1 a

  %hint total
  list1F : Functor List1
  list1F = %runElab derive

  %hint total
  list1M : Foldable List1
  list1M = %runElab derive

  total
  list1T : Traversable List1
  list1T = %runElab derive

namespace Full

  data Full a = Leaf a | Node (Full (a, a))

  %hint total
  fullF : Functor Full
  fullF = %runElab derive

  %hint total
  fullM : Foldable Full
  fullM = %runElab derive

  total
  fullT : Traversable Full
  fullT = %runElab derive

namespace LAZY

  record LAZY (a : Type) where
    constructor MkLAZY
    wrapped : Lazy a

  %hint total
  lazyF : Functor LAZY
  lazyF = %runElab derive

  %hint total
  lazyM : Foldable LAZY
  lazyM = %runElab derive

  total
  lazyT : Traversable LAZY
  lazyT = %runElab derive

namespace Rose

  data Rose a = Node (List (Lazy (Rose a)))

  %hint total
  roseF : Functor Rose
  roseF = %runElab derive

  %hint total
  roseM : Foldable Rose
  roseM = %runElab derive

  total
  roseT : Traversable Rose
  roseT = %runElab derive

namespace MaybeT

  record MaybeT (m : Type -> Type) (a : Type) where
    constructor MkMaybeT
    runMaybeT : m (Maybe a)

  %hint total
  maybeTF : Functor m => Functor (MaybeT m)
  maybeTF = %runElab derive

  %hint total
  maybeTM : Foldable m => Foldable (MaybeT m)
  maybeTM = %runElab derive

  total
  maybeTT : Traversable m => Traversable (MaybeT m)
  maybeTT = %runElab derive

namespace TreeT

  data TreeT : (Type -> Type -> Type) -> Type -> Type where
    MkTreeT : layer a (TreeT layer a) -> TreeT layer a

  %hint
  treeTF : Bifunctor layer => Functor (TreeT layer)
  treeTF = %runElab derive {treq = CoveringOnly}

  %hint
  treeTM : Bifoldable layer => Foldable (TreeT layer)
  treeTM = %runElab derive {treq = CoveringOnly}

  %hint
  treeTT : Bitraversable layer => Traversable (TreeT layer)
  treeTT = %runElab derive {treq = CoveringOnly}

  record Tree (a : Type) where
    constructor MkTree
    runTree : TreeT Either a

  %hint
  treeF : Functor Tree
  treeF = %runElab derive {treq = CoveringOnly}

  %hint
  treeM : Foldable Tree
  treeM = %runElab derive {treq = CoveringOnly}

  treeT : Traversable Tree
  treeT = %runElab derive {treq = CoveringOnly}

namespace Implicit

  data IVect : {n : Nat} -> (a : Type) -> Type where
    MkIVect : (v : Vect n a) -> IVect {n} a

  %hint total
  ivectF : {m : Nat} -> Functor (IVect {n = m})
  ivectF = %runElab derive

  %hint total
  ivectM : {m : Nat} -> Foldable (IVect {n = m})
  ivectM = %runElab derive

  total
  ivectT : {m : Nat} -> Traversable (IVect {n = m})
  ivectT = %runElab derive

namespace EqMap

  data EqMap : (key : Type) -> Eq key => (val : Type) -> Type where
    MkEqMap : (eq : Eq key) => List (key, val) -> EqMap key @{eq} val

  empty : Eq key => EqMap key val
  empty = MkEqMap []

  insert : (eq : Eq key) => key -> val -> EqMap key @{eq} val -> EqMap key @{eq} val
  insert k v (MkEqMap kvs) = MkEqMap ((k, v) :: filter ((k /=) . fst) kvs)

  fromList : Eq key => List (key, val) -> EqMap key val
  fromList = foldr (uncurry insert) empty

  toList : EqMap key @{eq} val -> List (key, val)
  toList (MkEqMap kvs) = kvs

  test : EqMap.toList (fromList [(1,2), (1,3), (2, 4), (5, 3), (1, 0)])
         === [(1,2), (2, 4), (5, 3)]
  test = Refl

  %hint total
  eqMapF : (eq : Eq key) => Functor (EqMap key @{eq})
  eqMapF = %runElab derive

  %hint total
  eqMapM : (eq : Eq key) => Foldable (EqMap key @{eq})
  eqMapM = %runElab derive

  total
  eqMapT : (eq : Eq key) => Traversable (EqMap key @{eq})
  eqMapT = %runElab derive

namespace Implicit

  data WithImplicits : Type -> Type where
    MkImplicit : {x : a} -> (0 y : a) -> WithImplicits a
    OtherImplicit : {0 x : a} -> a => WithImplicits a
    LastOne : {auto 0 _ : a} -> a -> WithImplicits a

  failing "Cannot traverse a runtime irrelevant value"

    total
    withImplicits : Traversable WithImplicits
    withImplicits = %runElab derive

failing "Couldn't find a `Traversable' instance for the type constructor DeriveTraversable.Wrap"

  record Wrap (a : Type) where
    constructor MkWrap
    unWrap : a

  %hint total
  wrapF : Functor Wrap
  wrapF = %runElab derive

  %hint total
  wrapM : Foldable Wrap
  wrapM = %runElab derive

  data Indirect : Type -> Type where
    MkIndirect : Wrap a -> Indirect a

  %hint total
  indirectF : Functor Indirect
  indirectF = %runElab derive

  %hint total
  indirectM : Foldable Indirect
  indirectM = %runElab derive

  total
  indirectT : Traversable Indirect
  indirectT = %runElab derive

namespace BitraversableFail

  data Tree : (l, n : Type) -> Type where
    Leaf : l -> Tree l n
    Node : Tree l n -> n -> Tree l n -> Tree l n

  -- this one will succeed
  %hint total
  treeF : Functor (Tree l)
  treeF = %runElab derive

  %hint total
  treeM : Foldable (Tree l)
  treeM = %runElab derive

  total
  tree : Traversable (Tree l)
  tree = %runElab derive

  failing "Couldn't find a `Bitraversable' instance for the type constructor DeriveTraversable.BitraversableFail.Tree"

    record Tree' (a : Type) where
      constructor MkTree'
      getTree : Tree a a

    -- and this one will fail
    tree' : Traversable Tree'
    tree' = %runElab derive

failing "Expected a type constructor, got: Prelude.Basics.id {a = Type}"

  total
  traverable : Traversable Prelude.id
  traverable = %runElab derive

namespace Triple

  data Triple a b c = MkTriple a b c

  %hint
  triple : Traversable (Triple a b)
  triple = %runElab derive

  data Tree3 a = Node (Triple a () (Tree3 a))

  failing "The term DeriveTraversable.Triple.Triple a Builtin.Unit is not free of a"

    tree : Traversable Tree3
    tree = %runElab derive

namespace WriterList

  data WList : (w, u, a : Type) -> Type where
    (::) : (w, a) -> WList {- oops -} a u a -> WList w u a
    Nil : WList w u a

  failing "The term DeriveTraversable.WriterList.WList a u is not free of a"

    wlist : Traversable (WList w ())
    wlist = %runElab derive

namespace WithImplicits

  data F : Type -> Type where
    MkF : {x : a} -> Nat -> a -> String -> {y : a} -> a -> List a -> F a

  %hint
  fF : Functor F
  fF = %runElab derive

  %hint
  fM : Foldable F
  fM = %runElab derive

  fT : Traversable F
  fT = %runElab derive
