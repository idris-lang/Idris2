module DeriveFunctor

import Deriving.Functor

%language ElabReflection
%default covering

%logging "derive.functor.clauses" 1
%logging "derive.functor.assumption" 10

list : Functor List
list = %runElab derive

maybe : Functor Maybe
maybe = %runElab derive

either : Functor (Either err)
either = %runElab derive

namespace Constant

  record Constant (a, b : Type) where
    constructor MkConstant
    runConstant : a

  constant : Functor (Constant a)
  constant = %runElab derive

namespace Vect

  public export
  data Vect : Nat -> Type -> Type where
    Nil : Vect Z a
    (::) : a -> Vect n a -> Vect (S n) a

  export %hint
  total
  vect : Functor (Vect n)
  vect = %runElab derive

namespace BigTree

  data BigTree a
    = End a
    | Branch String (List a) (Bool -> BigTree a)
    | Rose (List (BigTree a))

  total
  bigTree : Functor BigTree
  bigTree = %runElab derive

namespace Matrix

  record Matrix m n a where
    constructor MkMatrix
    runMatrix : Vect m (Vect n a)

  total
  matrix : Functor (Matrix m n)
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
  tm : Functor Tm
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

  %hint total tree : Functor Tree
  %hint total forest : Functor Forest

  tree = %runElab derive {mutualWith = [`{Forest}]}
  forest = %runElab derive {mutualWith = [`{Tree}]}

namespace List1

  data List1 : Type -> Type where
    MkList1 : (a, Maybe (List1 a)) -> List1 a

  total
  list1 : Functor List1
  list1 = %runElab derive

namespace Full

  data Full a = Leaf a | Node (Full (a, a))

  total
  full : Functor Full
  full = %runElab derive

failing "Negative occurrence of a"

  data NOT : Type -> Type where
    MkNOT : (a -> Void) -> NOT a

  total
  negative : Functor NOT
  negative = %runElab derive

namespace Colist

  data Colist a = Nil | (::) a (Inf (Colist a))

  total
  colist : Functor Colist
  colist = %runElab derive

namespace LAZY

  record LAZY (a : Type) where
    constructor MkLAZY
    wrapped : Lazy a

  total
  lazy : Functor LAZY
  lazy = %runElab derive

namespace Rose

  data Rose a = Node (List (Lazy (Rose a)))

  total
  rose : Functor Rose
  rose = %runElab derive

namespace Free

  data Free : (Type -> Type) -> Type -> Type where
    Pure : a -> Free f a
    Bind : f a -> (a -> Free f b) -> Free f b

  total
  free : Functor (Free f)
  free = %runElab derive

namespace MaybeT

  record MaybeT (m : Type -> Type) (a : Type) where
    constructor MkMaybeT
    runMaybeT : m (Maybe a)

  total
  maybeT : Functor m => Functor (MaybeT m)
  maybeT = %runElab derive

namespace TreeT

  data TreeT : (Type -> Type -> Type) -> Type -> Type where
    MkTreeT : layer a (TreeT layer a) -> TreeT layer a

  %hint
  treeT : Bifunctor layer => Functor (TreeT layer)
  treeT = %runElab derive {treq = CoveringOnly}

  record Tree (a : Type) where
    constructor MkTree
    runTree : TreeT Either a

  tree : Functor Tree
  tree = %runElab derive {treq = CoveringOnly}

namespace Implicit

  data IVect : {n : Nat} -> (a : Type) -> Type where
    MkIVect : (v : Vect n a) -> IVect {n} a

  ivect : {m : Nat} -> Functor (IVect {n = m})
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

  eqMap : (eq : Eq key) => Functor (EqMap key @{eq})
  eqMap = %runElab derive

namespace Cont

  data Cont r a = MkCont ((a -> r) -> r)

  cont : Functor (Cont r)
  cont = %runElab derive

  ||| Continuation with short-circuiting error cont
  data Cont2 r e a = MkCont2 ((e -> r) -> (a -> r) -> r)

  cont2 : Functor (Cont2 r e)
  cont2 = %runElab derive

  ||| Uncurried version of continuation with short-circuiting error cont
  data Cont2' r e a = MkCont2' (((a -> r), (e -> r)) -> r)

  cont2' : Functor (Cont2' r e)
  cont2' = %runElab derive

  ||| Throw in lazyness
  data Cont2'' r e a = MkCont2'' (Lazy ((Lazy a -> r), (e -> r)) -> r)

  cont2'' : Functor (Cont2'' r e)
  cont2'' = %runElab derive

failing "Couldn't find a `Functor' instance for the type constructor DeriveFunctor.Wrap"

  record Wrap (a : Type) where
    constructor MkWrap
    unWrap : a

  data Indirect : Type -> Type where
    MkIndirect : Wrap a -> Indirect a

  total
  indirect : Functor Indirect
  indirect = %runElab derive

namespace BifunctorFail

  data Tree : (l, n : Type) -> Type where
    Leaf : l -> Tree l n
    Node : Tree l n -> n -> Tree l n -> Tree l n

  -- this one will succeed
  total
  tree : Functor (Tree l)
  tree = %runElab derive

  failing "Couldn't find a `Bifunctor' instance for the type constructor DeriveFunctor.BifunctorFail.Tree"

    record Tree' (a : Type) where
      constructor MkTree'
      getTree : Tree a a

    -- and this one will fail
    tree' : Functor Tree'
    tree' = %runElab derive

failing "Expected a type constructor, got: Prelude.Basics.id {a = Type}"

  total
  functor : Functor Prelude.id
  functor = %runElab derive

namespace Triple

  data Triple a b c = MkTriple a b c

  %hint
  triple : Functor (Triple a b)
  triple = %runElab derive

  data Tree3 a = Node (Triple a () (Tree3 a))

  failing "The term DeriveFunctor.Triple.Triple a Builtin.Unit is not free of a"

    tree : Functor Tree3
    tree = %runElab derive

namespace WriterList

  data WList : (w, u, a : Type) -> Type where
    (::) : (w, a) -> WList {- oops -} a u a -> WList w u a
    Nil : WList w u a

  failing "The term DeriveFunctor.WriterList.WList a u is not free of a"

    wlist : Functor (WList w ())
    wlist = %runElab derive
