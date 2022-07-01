module DeriveFunctor

import Deriving.Functor

%language ElabReflection
%default total

%logging "derive.functor.clauses" 1

list : Functor List
list = %runElab derive

maybe : Functor Maybe
maybe = %runElab derive

either : Functor (Either err)
either = %runElab derive

namespace Vect

  public export
  data Vect : Nat -> Type -> Type where
    Nil : Vect Z a
    (::) : a -> Vect n a -> Vect (S n) a

  export %hint
  vect : Functor (Vect n)
  vect = %runElab derive

namespace BigTree

  data BigTree a
    = End a
    | Branch String (List a) (Bool -> BigTree a)
    | Rose (List (BigTree a))

  bigTree : Functor BigTree
  bigTree = %runElab derive

namespace Matrix

  record Matrix m n a where
    constructor MkMatrix
    runMatrix : Vect m (Vect n a)

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

  %hint tree : Functor Tree
  %hint forest : Functor Forest

  tree = %runElab derive {mutualWith = [`{Forest}]}
  forest = %runElab derive {mutualWith = [`{Tree}]}

namespace List1

  data List1 : Type -> Type where
    MkList1 : (a, Maybe (List1 a)) -> List1 a

  list1 : Functor List1
  list1 = %runElab derive

namespace Full

  data Full a = Leaf a | Node (Full (a, a))

  full : Functor Full
  full = %runElab derive

failing "Negative occurence of a"

  data NOT : Type -> Type where
    MkNOT : (a -> Void) -> NOT a

  negative : Functor NOT
  negative = %runElab derive

namespace Colist

  data Colist a = Nil | (::) a (Inf (Colist a))

  colist : Functor Colist
  colist = %runElab derive


namespace LAZY

  record LAZY (a : Type) where
    constructor MkLAZY
    wrapped : Lazy a

  lazy : Functor LAZY
  lazy = %runElab derive
