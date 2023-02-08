module DeriveFoldable

import Deriving.Foldable

%language ElabReflection
%default covering

%logging "derive.foldable.clauses" 1
%logging "derive.foldable.assumption" 10

list : Foldable List
list = %runElab derive

maybe : Foldable Maybe
maybe = %runElab derive

either : Foldable (Either err)
either = %runElab derive

pair : Foldable (Pair a)
pair = %runElab derive

namespace Constant

  record Constant (a, b : Type) where
    constructor MkConstant
    runConstant : a

  constant : Foldable (Constant a)
  constant = %runElab derive

namespace Vect

  public export
  data Vect : Nat -> Type -> Type where
    Nil : Vect Z a
    (::) : a -> Vect n a -> Vect (S n) a

  export %hint
  total
  vect : Foldable (Vect n)
  vect = %runElab derive

namespace BigTree

  data BigTree a
    = End a
    | Branch String (List a) (Bool -> BigTree a)
      -- this (Bool ->) is problematic, at least until we have an interface for finite types
    | Rose (List (BigTree a))

  failing "Unsupported type"
    total
    bigTree : Foldable BigTree
    bigTree = %runElab derive

namespace Matrix

  record Matrix m n a where
    constructor MkMatrix
    runMatrix : Vect m (Vect n a)

  total
  matrix : Foldable (Matrix m n)
  matrix = %runElab derive

namespace Tm

  data Op : Nat -> Type where
    Neg : Op 1
    Add : Op 2

  data Tm : Type -> Type where
    Var : a -> Tm a
    Call : Op n -> Vect n (Tm a) -> Tm a
    Lam : Tm (Maybe a) -> Tm a

  total
  tm : Foldable Tm
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

  %hint total tree : Foldable Tree
  %hint total forest : Foldable Forest

  tree = %runElab derive {mutualWith = [`{Forest}]}
  forest = %runElab derive {mutualWith = [`{Tree}]}

namespace List1

  %hide List1

  data List1 : Type -> Type where
    MkList1 : (a, Maybe (List1 a)) -> List1 a

  total
  list1 : Foldable List1
  list1 = %runElab derive

namespace Full

  data Full a = Leaf a | Node (Full (a, a))

  total
  full : Foldable Full
  full = %runElab derive

namespace Colist

  data Colist a = Nil | (::) a (Inf (Colist a))

  failing "Cannot fold over an infinite structure"

    total
    colist : Foldable Colist
    colist = %runElab derive

namespace LAZY

  record LAZY (a : Type) where
    constructor MkLAZY
    wrapped : Lazy a

  total
  lazy : Foldable LAZY
  lazy = %runElab derive

namespace Rose

  data Rose a = Node (List (Lazy (Rose a)))

  total
  rose : Foldable Rose
  rose = %runElab derive

namespace Free

  data Free : (Type -> Type) -> Type -> Type where
    Pure : a -> Free f a
    Bind : f a -> (a -> Free f b) -> Free f b

  -- Once again the pi type prevents us from defining Foldable
  failing "Unsupported type"

    total
    free : Foldable (Free f)
    free = %runElab derive

namespace MaybeT

  record MaybeT (m : Type -> Type) (a : Type) where
    constructor MkMaybeT
    runMaybeT : m (Maybe a)

  total
  maybeT : Foldable m => Foldable (MaybeT m)
  maybeT = %runElab derive

namespace TreeT

  data TreeT : (lbl : Type) -> (Type -> Type -> Type) -> Type -> Type where
    MkTreeT : lbl -> layer a (TreeT lbl layer a) -> TreeT lbl layer a

  %hint
  treeT : Bifoldable layer => Foldable (TreeT lbl layer)
  treeT = %runElab derive {treq = CoveringOnly}

  record Tree (a : Type) where
    constructor MkTree
    runTree : TreeT () Either a

  tree : Foldable Tree
  tree = %runElab derive {treq = CoveringOnly}

namespace Implicit

  data IVect : {n : Nat} -> (a : Type) -> Type where
    MkIVect : (v : Vect n a) -> IVect {n} a

  ivect : {m : Nat} -> Foldable (IVect {n = m})
  ivect = %runElab derive

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

  eqMap : (eq : Eq key) => Foldable (EqMap key @{eq})
  eqMap = %runElab derive

namespace Implicit

  data WithImplicits : Type -> Type where
    MkImplicit : {x : a} -> (0 y : a) -> WithImplicits a
    OtherImplicit : {0 x : a} -> a => WithImplicits a
    LastOne : {auto 0 _ : a} -> a -> WithImplicits a

  failing "Cannot fold over a runtime irrelevant value"

    total
    withImplicits : Foldable WithImplicits
    withImplicits = %runElab derive

failing "Couldn't find a `Foldable' instance for the type constructor DeriveFoldable.Wrap"

  record Wrap (a : Type) where
    constructor MkWrap
    unWrap : a

  data Indirect : Type -> Type where
    MkIndirect : Wrap a -> Indirect a

  total
  indirect : Foldable Indirect
  indirect = %runElab derive

namespace BifoldableFail

  data Tree : (l, n : Type) -> Type where
    Leaf : l -> Tree l n
    Node : Tree l n -> n -> Tree l n -> Tree l n

  -- this one will succeed
  total
  tree : Foldable (Tree l)
  tree = %runElab derive

  failing "Couldn't find a `Bifoldable' instance for the type constructor DeriveFoldable.BifoldableFail.Tree"

    record Tree' (a : Type) where
      constructor MkTree'
      getTree : Tree a a

    -- and this one will fail
    tree' : Foldable Tree'
    tree' = %runElab derive

failing "Expected a type constructor, got: Prelude.Basics.id {a = Type}"

  total
  foldable : Foldable Prelude.id
  foldable = %runElab derive

namespace Triple

  data Triple a b c = MkTriple a b c

  %hint
  triple : Foldable (Triple a b)
  triple = %runElab derive

  data Tree3 a = Node (Triple a () (Tree3 a))

  failing "The term DeriveFoldable.Triple.Triple a Builtin.Unit is not free of a"

    tree : Foldable Tree3
    tree = %runElab derive

namespace WriterList

  data WList : (w, u, a : Type) -> Type where
    (::) : (w, a) -> WList {- oops -} a u a -> WList w u a
    Nil : WList w u a

  failing "The term DeriveFoldable.WriterList.WList a u is not free of a"

    wlist : Foldable (WList w ())
    wlist = %runElab derive
