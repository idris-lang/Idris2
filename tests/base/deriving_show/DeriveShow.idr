module DeriveShow

import Deriving.Show

%language ElabReflection
%default covering

%logging "derive.show.clauses" 1
%logging "derive.show.assumption" 10

namespace Enum

  data Enum = A | B | C

  enumShow : Show Enum
  enumShow = %runElab derive

namespace Sum

  data Sum : Type where
    AString : String -> Sum
    ANat : Nat -> Sum

  sumShow : Show Sum
  sumShow = %runElab derive

list : Show a => Show (List a)
list = %runElab derive

maybe : Show a => Show (Maybe a)
maybe = %runElab derive

either : (Show err, Show a) => Show (Either err a)
either = %runElab derive

namespace Constant

  record Constant (a, b : Type) where
    constructor MkConstant
    runConstant : a

  constant : Show a => Show (Constant a b)
  constant = %runElab derive

namespace Vect

  public export
  data Vect : Nat -> Type -> Type where
    Nil : Vect Z a
    (::) : a -> Vect n a -> Vect (S n) a

  export %hint
  total
  vect : Show a => Show (Vect n a)
  vect = %runElab derive

namespace BigTree

  data BigTree a
    = End a
    | Branch String (List a) (Bool -> BigTree a)
    | Rose (List (BigTree a))

  failing "Unsupported type"
    bigTree : Show a => Show (BigTree a)
    bigTree = %runElab derive

namespace Matrix

  record Matrix m n a where
    constructor MkMatrix
    runMatrix : Vect m (Vect n a)

  total
  matrix : Show a => Show (Matrix m n a)
  matrix = %runElab derive

namespace Tm

  public export
  data Op : Nat -> Type where
    Neg : Op 1
    Add : Op 2

  %hint
  op : Show (Op n)
  op = %runElab derive

  public export
  data Tm : Type -> Type where
    Var : a -> Tm a
    Call : Op n -> Vect n (Tm a) -> Tm a
    Lam : Tm (Maybe a) -> Tm a

  public export total %hint
  tm : Show a => Show (Tm a)
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

  %hint total tree : Show a => Show (Tree a)
  %hint total forest : Show a => Show (Forest a)

  tree = %runElab derive {mutualWith = [`{Forest}]}
  forest = %runElab derive {mutualWith = [`{Tree}]}

namespace List1

  data List1 : Type -> Type where
    MkList1 : (a, Maybe (List1 a)) -> List1 a

  total %hint
  list1 : Show a => Show (List1 a)
  list1 = %runElab derive

namespace Full

  data Full a = Leaf a | Node (Full (a, a))

  total %hint
  full : Show a => Show (Full a)
  full = %runElab derive

failing "Unsupported type"

  data NOT : Type -> Type where
    MkNOT : (a -> Void) -> NOT a

  total
  negative : Show a => Show (NOT a)
  negative = %runElab derive

namespace Colist

  data Colist a = Nil | (::) a (Inf (Colist a))

  failing "Cannot show an infinite structure"

    total
    colist : Show a => Show (Colist a)
    colist = %runElab derive

namespace LAZY

  record LAZY (a : Type) where
    constructor MkLAZY
    wrapped : Lazy a

  total
  lazy : Show a => Show (LAZY a)
  lazy = %runElab derive

namespace Implicit

  data IVect : {n : Nat} -> (a : Type) -> Type where
    MkIVect : (v : Vect n a) -> IVect {n} a

  ivect : {m : Nat} -> Show a => Show (IVect {n = m} a)
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

  eqMap : (eq : Eq key) => Show key => Show val => Show (EqMap key @{eq} val)
  eqMap = %runElab derive

namespace Reducible

  Y : Bool -> Type
  Y True  = Bool
  Y False = Nat

  data X : Type where
    X0 : X
    X1 : Bool -> X
    X2 : Y True -> Y False -> X

  x : Show X
  x = %runElab derive
