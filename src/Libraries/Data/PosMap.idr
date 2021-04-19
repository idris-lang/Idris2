||| Specialized implementation of an interval map with finger trees [1].
||| This data structure is meant to get efficiently data with a correlated NonEmptyFC.
||| The element data type must implement the `Measure` interface. An implementation
||| is provided already for NonEmptyFC and tuples with NonEmptyFC as first element.
|||
||| [1] https://www.staff.city.ac.uk/~ross/papers/FingerTree.pdf
module Libraries.Data.PosMap

import Data.List
import Core.FC

%default total

infixr 5 <|, <:
infixl 5 |>, :>

public export
FileRange : Type
FileRange = (FilePos, FilePos)

||| Type for rightmost intervals, ordered by their low endpoints and annotated
||| with the maximum of the high endpoints.
data RMFileRange = MkRange FileRange FilePos

Eq RMFileRange where
  (MkRange low high) == (MkRange low' high') = low == low' && high == high'

Show RMFileRange where
  showPrec p (MkRange low high) = showCon p "MkRange" $ showArg low ++ showArg high

Semigroup RMFileRange where
  -- The semigroup operation on righmost intervals is the composition of two
  -- monoids applied to each component:
  -- 1) the operation on low endpoints always returns the last key it contains,
  --    assuming the keys are ordered (enforced by the insertion function), the
  --    FingerTree behaves as a store of ordered sequences, with measures
  --    serving as signpost keys.
  -- 2) the operation on high endpoints returns the maximum of the endpoints,
  --    thus the FingerTree behaves as a max-priority queue.
  (MkRange low high) <+> (MkRange low' high') = MkRange low' (max high high')

data Interval = MkInterval RMFileRange | NoInterval

Eq Interval where
  (MkInterval range) == (MkInterval range') = range == range'
  NoInterval == NoInterval = True
  _ == _ = False

Show Interval where
  showPrec p (MkInterval range) = showCon p "MkInterval" $ showArg range
  showPrec p NoInterval = "NoInterval"

Semigroup Interval where
  NoInterval <+> i = i
  i <+> NoInterval = i
  (MkInterval range) <+> (MkInterval range') = MkInterval (range <+> range')

Monoid Interval where
  neutral = NoInterval

Cast FileRange RMFileRange where
  cast (l, h) = MkRange (l, h) h

Cast FileRange Interval where
  cast (l, h) = MkInterval (MkRange (l, h) h)

Cast RMFileRange Interval where
  cast = MkInterval

||| Things that have an associated interval in the source files.
public export
interface Measure a where
  measure : a -> FileRange

interface MeasureRM a where
  measureRM : a -> RMFileRange

public export
Measure a => MeasureRM a where
  measureRM = cast . measure

measureInterval : Measure a => a -> Interval
measureInterval = cast . measure

data Digit : Type -> Type where
  One : a -> Digit a
  Two : a -> a -> Digit a
  Three : a -> a -> a -> Digit a
  Four : a -> a -> a -> a -> Digit a

Eq a => Eq (Digit a) where
  (One x) == (One x') = x == x'
  (Two x y) == (Two x' y') = x == x' && y == y'
  (Three x y z) == (Three x' y' z') = x == x' && y == y' && z == z'
  (Four x y z w) == (Four x' y' z' w') = x == x' && y == y' && z == z' && w == w'
  _ == _ = False

Show a => Show (Digit a) where
  showPrec p (One x) = showCon p "One" $ showArg x
  showPrec p (Two x y) = showCon p "Two" $ showArg x ++ showArg y
  showPrec p (Three x y z) = showCon p "Three" $ showArg x ++ showArg y ++ showArg z
  showPrec p (Four x y z w) = showCon p "Four" $ showArg x ++ showArg y ++ showArg z ++ showArg w

Functor Digit where
  map f (One x) = One (f x)
  map f (Two x y) = Two (f x) (f y)
  map f (Three x y z) = Three (f x) (f y) (f z)
  map f (Four x y z w) = Four (f x) (f y) (f z) (f w)

Foldable Digit where
  foldr f init (One a) = f a init
  foldr f init (Two a b) = f a (f b init)
  foldr f init (Three a b c) = f a (f b (f c init))
  foldr f init (Four a b c d) = f a (f b (f c (f d init)))

  foldl f init (One a) = f init a
  foldl f init (Two a b) = f (f init a) b
  foldl f init (Three a b c) = f (f (f init a) b) c
  foldl f init (Four a b c d) = f (f (f (f init a) b) c) d

  null _ = False

Traversable Digit where
  traverse f (One x) = [| One (f x) |]
  traverse f (Two x y) = [| Two (f x) (f y) |]
  traverse f (Three x y z) = [| Three (f x) (f y) (f z) |]
  traverse f (Four x y z w) = [| Four (f x) (f y) (f z) (f w) |]

MeasureRM a => MeasureRM (Digit a) where
  measureRM (One x) = measureRM x
  measureRM (Two x y) = measureRM x <+> measureRM y
  measureRM (Three x y z) = measureRM x <+> measureRM y <+> measureRM z
  measureRM (Four x y z w) = measureRM x <+> measureRM y <+> measureRM z <+> measureRM w

data Node : Type -> Type where
  Node2 : RMFileRange -> a -> a -> Node a
  Node3 : RMFileRange -> a -> a -> a -> Node a

node2 : MeasureRM a => a -> a -> Node a
node2 x y = Node2 (measureRM x <+> measureRM y) x y

node3 : MeasureRM a => a -> a -> a -> Node a
node3 x y z = Node3 (measureRM x <+> measureRM y <+> measureRM z) x y z

Foldable Node where
  foldr f init (Node2 _ x y) = f x (f y init)
  foldr f init (Node3 _ x y z) = f x (f y (f z init))

  foldl f init (Node2 v a b) = f (f init a) b
  foldl f init (Node3 v a b c) = f (f (f init a) b) c

MeasureRM (Node a) where
  measureRM (Node2 v {}) = v
  measureRM (Node3 v {}) = v

namespace Node
  export
  map : MeasureRM b => (a -> b) -> Node a -> Node b
  map f (Node2 _ x y) = node2 (f x) (f y)
  map f (Node3 _ x y z) = node3 (f x) (f y) (f z)

  export
  traverse : (Applicative f, MeasureRM b) => (a -> f b) -> Node a -> f (Node b)
  traverse f (Node2 _ x y) = [| node2 (f x) (f y) |]
  traverse f (Node3 _ x y z) = [| node3 (f x) (f y) (f z) |]

nodeToDigit : MeasureRM a => Node a -> Digit a
nodeToDigit (Node2 _ x y) = Two x y
nodeToDigit (Node3 _ x y z) = Three x y z

export
data PosMap : Type -> Type where
  Empty : PosMap a
  Single : a -> PosMap a
  Deep : RMFileRange -> Digit a -> PosMap (Node a) -> Digit a -> PosMap a

measureTree : MeasureRM a => PosMap a -> Interval
measureTree Empty = neutral
measureTree (Single x) = cast (measureRM x)
measureTree (Deep v {}) = cast v

addIntervalRight : RMFileRange -> Interval -> RMFileRange
addIntervalRight range (MkInterval range') = range <+> range'
addIntervalRight range NoInterval = range

addIntervalLeft : Interval -> RMFileRange -> RMFileRange
addIntervalLeft (MkInterval range) range' = range <+> range'
addIntervalLeft NoInterval range' = range'

deep : MeasureRM a => Digit a -> PosMap (Node a) -> Digit a -> PosMap a
deep pr t sf = Deep value pr t sf
  where value : RMFileRange
        value = case measureTree t of
                     MkInterval range => measureRM pr <+> range <+> measureRM sf
                     NoInterval => measureRM pr <+> measureRM sf

digitToTree : MeasureRM a => Digit a -> PosMap a
digitToTree (One a) = Single a
digitToTree (Two a b) = deep (One a) Empty (One b)
digitToTree (Three a b c) = deep (Two a b) Empty (One c)
digitToTree (Four a b c d) = deep (Two a b) Empty (Two c d)

(<|) : MeasureRM a => a -> PosMap a -> PosMap a
a <| Empty                        = Single a
a <| (Single b)                   = deep (One a) Empty (One b)
a <| (Deep _ (One b) m sf)        = deep (Two a b) m sf
a <| (Deep _ (Two b c) m sf)      = deep (Three a b c) m sf
a <| (Deep _ (Three b c d) m sf)  = deep (Four a b c d) m sf
a <| (Deep _ (Four b c d e) m sf) = deep (Two a b) (node3 c d e <| m) sf

(|>) : MeasureRM a => PosMap a -> a -> PosMap a
Empty                        |> a = Single a
(Single b)                   |> a = deep (One b) Empty (One a)
(Deep _ pr m (One b))        |> a = deep pr m (Two b a)
(Deep _ pr m (Two c b))      |> a = deep pr m (Three c b a)
(Deep _ pr m (Three d c b))  |> a = deep pr m (Four d c b a)
(Deep _ pr m (Four e d c b)) |> a = deep pr (m |> node3 e d c) (Two b a)

export
Foldable PosMap where
  foldr f init Empty = init
  foldr f init (Single x) = f x init
  foldr f init (Deep _ pr m sf) = foldr f (foldr (flip (foldr f)) (foldr f init sf) m) pr

  foldl f init Empty = init
  foldl f init (Single x) = f init x
  foldl f init (Deep _ pr m sf) = foldl f (foldl (foldl f) (foldl f init pr) m) sf

  null Empty = True
  null (Single {}) = False
  null (Deep {}) = False

export
empty : PosMap a
empty = Empty

export
singleton : a -> PosMap a
singleton x = Single x

toTree : (Foldable f, MeasureRM a) => f a -> PosMap a
toTree xs = foldr (<|) empty xs

data ViewL : Type -> Type where
  EmptyL : ViewL a
  (<:) : a -> PosMap a -> ViewL a

rotl : MeasureRM a => PosMap (Node a) -> Digit a -> PosMap a
viewl : MeasureRM a => PosMap a -> ViewL a

rotl t sf =
  case viewl t of
       EmptyL => digitToTree sf
       a <: t' => case measureTree t of
                       MkInterval range => Deep (range <+> measureRM sf) (nodeToDigit a) t' sf
                       NoInterval => Deep (measureRM sf) (nodeToDigit a) t' sf

viewl Empty = EmptyL
viewl (Single x) = x <: Empty
viewl (Deep _ (One x) t sf) = x <: rotl t sf
viewl (Deep _ (Two x y) t sf) = x <: deep (One y) t sf
viewl (Deep _ (Three x y z) t sf) = x <: deep (Two y z) t sf
viewl (Deep _ (Four x y z w) t sf) = x <: deep (Three y z w) t sf

data ViewR : Type -> Type where
  EmptyR : ViewR a
  (:>) : PosMap a -> a -> ViewR a

rotr : MeasureRM a => Digit a -> PosMap (Node a) -> PosMap a
viewr : MeasureRM a => PosMap a -> ViewR a

rotr pr t =
  case viewr t of
       EmptyR => digitToTree pr
       t' :> a => case measureTree t of
                       MkInterval range => Deep (measureRM pr <+> range) pr t' (nodeToDigit a)
                       NoInterval => Deep (measureRM pr) pr t' (nodeToDigit a)

viewr Empty = EmptyR
viewr (Single x) = Empty :> x
viewr (Deep _ pr t (One x)) = rotr pr t :> x
viewr (Deep _ pr t (Two x y)) = deep pr t (One x) :> y
viewr (Deep _ pr t (Three x y z)) = deep pr t (Two x y) :> z
viewr (Deep _ pr t (Four x y z w)) = deep pr t (Three x y z) :> w

appendTree0 : MeasureRM a => PosMap a -> PosMap a -> PosMap a
appendTree1 : MeasureRM a => PosMap a -> a -> PosMap a -> PosMap a
appendTree2 : MeasureRM a => PosMap a -> a -> a -> PosMap a -> PosMap a
appendTree3 : MeasureRM a => PosMap a -> a -> a -> a -> PosMap a -> PosMap a
appendTree4 : MeasureRM a => PosMap a -> a -> a -> a -> a -> PosMap a -> PosMap a
addDigits0  : MeasureRM a => PosMap (Node a) -> Digit a -> Digit a -> PosMap (Node a) -> PosMap (Node a)
addDigits1  : MeasureRM a => PosMap (Node a) -> Digit a -> a -> Digit a -> PosMap (Node a) -> PosMap (Node a)
addDigits2  : MeasureRM a => PosMap (Node a) -> Digit a -> a -> a -> Digit a -> PosMap (Node a) -> PosMap (Node a)
addDigits3  : MeasureRM a => PosMap (Node a) -> Digit a -> a -> a -> a -> Digit a -> PosMap (Node a) -> PosMap (Node a)
addDigits4  : MeasureRM a => PosMap (Node a) -> Digit a -> a -> a -> a -> a -> Digit a -> PosMap (Node a) -> PosMap (Node a)

appendTree0 Empty xs = xs
appendTree0 xs Empty = xs
appendTree0 (Single x) xs = x <| xs
appendTree0 xs (Single x) = xs |> x
appendTree0 (Deep _ pr1 t1 sf1) (Deep _ pr2 t2 sf2) = deep pr1 (addDigits0 t1 sf1 pr2 t2) sf2

appendTree1 Empty a xs = a <| xs
appendTree1 xs a Empty = xs |> a
appendTree1 (Single x) a xs = x <| a <| xs
appendTree1 xs a (Single x) = xs |> a |> x
appendTree1 (Deep _ pr1 t1 sf1) a (Deep _ pr2 t2 sf2) = deep pr1 (addDigits1 t1 sf1 a pr2 t2) sf2

appendTree2 Empty a b xs = a <| b <| xs
appendTree2 xs a b Empty = xs |> a |> b
appendTree2 (Single x) a b xs = x <| a <| b <| xs
appendTree2 xs a b (Single x) = xs |> a |> b |> x
appendTree2 (Deep _ pr1 t1 sf1) a b (Deep _ pr2 t2 sf2) = deep pr1 (addDigits2 t1 sf1 a b pr2 t2) sf2

appendTree3 Empty a b c xs = a <| b <| c <| xs
appendTree3 xs a b c Empty = xs |> a |> b |> c
appendTree3 (Single x) a b c xs = x <| a <| b <| c <| xs
appendTree3 xs a b c (Single x) = xs |> a |> b |> c |> x
appendTree3 (Deep _ pr1 t1 sf1) a b c (Deep _ pr2 t2 sf2) = deep pr1 (addDigits3 t1 sf1 a b c pr2 t2) sf2

appendTree4 Empty a b c d xs = a <| b <| c <| d <| xs
appendTree4 xs a b c d Empty = xs |> a |> b |> c |> d
appendTree4 (Single x) a b c d xs = a <| b <| c <| d <| x <| xs
appendTree4 xs a b c d (Single x) = xs |> a |> b |> c |> d |> x
appendTree4 (Deep _ pr1 m1 sf1) a b c d (Deep _ pr2 m2 sf2) = deep pr1 (addDigits4 m1 sf1 a b c d pr2 m2) sf2

addDigits0 t1 (One a)        (One b)        t2 = appendTree1 t1 (node2 a b) t2
addDigits0 t1 (One a)        (Two b c)      t2 = appendTree1 t1 (node3 a b c) t2
addDigits0 t1 (One a)        (Three b c d)  t2 = appendTree2 t1 (node2 a b) (node2 c d) t2
addDigits0 t1 (One a)        (Four b c d e) t2 = appendTree2 t1 (node3 a b c) (node2 d e) t2
addDigits0 t1 (Two a b)      (One c)        t2 = appendTree1 t1 (node3 a b c) t2
addDigits0 t1 (Two a b)      (Two c d)      t2 = appendTree2 t1 (node2 a b) (node2 c d) t2
addDigits0 t1 (Two a b)      (Three c d e)  t2 = appendTree2 t1 (node3 a b c) (node2 d e) t2
addDigits0 t1 (Two a b)      (Four c d e f) t2 = appendTree2 t1 (node3 a b c) (node3 d e f) t2
addDigits0 t1 (Three a b c)  (One d)        t2 = appendTree2 t1 (node2 a b) (node2 c d) t2
addDigits0 t1 (Three a b c)  (Two d e)      t2 = appendTree2 t1 (node3 a b c) (node2 d e) t2
addDigits0 t1 (Three a b c)  (Three d e f)  t2 = appendTree2 t1 (node3 a b c) (node3 d e f) t2
addDigits0 t1 (Three a b c)  (Four d e f g) t2 = appendTree3 t1 (node3 a b c) (node2 d e) (node2 f g) t2
addDigits0 t1 (Four a b c d) (One e)        t2 = appendTree2 t1 (node3 a b c) (node2 d e) t2
addDigits0 t1 (Four a b c d) (Two e f)      t2 = appendTree2 t1 (node3 a b c) (node3 d e f) t2
addDigits0 t1 (Four a b c d) (Three e f g)  t2 = appendTree3 t1 (node3 a b c) (node2 d e) (node2 f g) t2
addDigits0 t1 (Four a b c d) (Four e f g h) t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node2 g h) t2

addDigits1 t1 (One a)        b (One c)        t2 = appendTree1 t1 (node3 a b c) t2
addDigits1 t1 (One a)        b (Two c d)      t2 = appendTree2 t1 (node2 a b) (node2 c d) t2
addDigits1 t1 (One a)        b (Three c d e)  t2 = appendTree2 t1 (node3 a b c) (node2 d e) t2
addDigits1 t1 (One a)        b (Four c d e f) t2 = appendTree2 t1 (node3 a b c) (node3 d e f) t2
addDigits1 t1 (Two a b)      c (One d)        t2 = appendTree2 t1 (node2 a b) (node2 c d) t2
addDigits1 t1 (Two a b)      c (Two d e)      t2 = appendTree2 t1 (node3 a b c) (node2 d e) t2
addDigits1 t1 (Two a b)      c (Three d e f)  t2 = appendTree2 t1 (node3 a b c) (node3 d e f) t2
addDigits1 t1 (Two a b)      c (Four d e f g) t2 = appendTree3 t1 (node3 a b c) (node2 d e) (node2 f g) t2
addDigits1 t1 (Three a b c)  d (One e)        t2 = appendTree2 t1 (node3 a b c) (node2 d e) t2
addDigits1 t1 (Three a b c)  d (Two e f)      t2 = appendTree2 t1 (node3 a b c) (node3 d e f) t2
addDigits1 t1 (Three a b c)  d (Three e f g)  t2 = appendTree3 t1 (node3 a b c) (node2 d e) (node2 f g) t2
addDigits1 t1 (Three a b c)  d (Four e f g h) t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node2 g h) t2
addDigits1 t1 (Four a b c d) e (One f)        t2 = appendTree2 t1 (node3 a b c) (node3 d e f) t2
addDigits1 t1 (Four a b c d) e (Two f g)      t2 = appendTree3 t1 (node3 a b c) (node2 d e) (node2 f g) t2
addDigits1 t1 (Four a b c d) e (Three f g h)  t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node2 g h) t2
addDigits1 t1 (Four a b c d) e (Four f g h i) t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node3 g h i) t2

addDigits2 t1 (One a)        b c (One d)        t2 = appendTree2 t1 (node2 a b) (node2 c d) t2
addDigits2 t1 (One a)        b c (Two d e)      t2 = appendTree2 t1 (node3 a b c) (node2 d e) t2
addDigits2 t1 (One a)        b c (Three d e f)  t2 = appendTree2 t1 (node3 a b c) (node3 d e f) t2
addDigits2 t1 (One a)        b c (Four d e f g) t2 = appendTree3 t1 (node3 a b c) (node2 d e) (node2 f g) t2
addDigits2 t1 (Two a b)      c d (One e)        t2 = appendTree2 t1 (node3 a b c) (node2 d e) t2
addDigits2 t1 (Two a b)      c d (Two e f)      t2 = appendTree2 t1 (node3 a b c) (node3 d e f) t2
addDigits2 t1 (Two a b)      c d (Three e f g)  t2 = appendTree3 t1 (node3 a b c) (node2 d e) (node2 f g) t2
addDigits2 t1 (Two a b)      c d (Four e f g h) t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node2 g h) t2
addDigits2 t1 (Three a b c)  d e (One f)        t2 = appendTree2 t1 (node3 a b c) (node3 d e f) t2
addDigits2 t1 (Three a b c)  d e (Two f g)      t2 = appendTree3 t1 (node3 a b c) (node2 d e) (node2 f g) t2
addDigits2 t1 (Three a b c)  d e (Three f g h)  t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node2 g h) t2
addDigits2 t1 (Three a b c)  d e (Four f g h i) t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node3 g h i) t2
addDigits2 t1 (Four a b c d) e f (One g)        t2 = appendTree3 t1 (node3 a b c) (node2 d e) (node2 f g) t2
addDigits2 t1 (Four a b c d) e f (Two g h)      t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node2 g h) t2
addDigits2 t1 (Four a b c d) e f (Three g h i)  t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node3 g h i) t2
addDigits2 t1 (Four a b c d) e f (Four g h i j) t2 = appendTree4 t1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) t2

addDigits3 t1 (One a)        b c d (One e)        t2 = appendTree2 t1 (node3 a b c) (node2 d e) t2
addDigits3 t1 (One a)        b c d (Two e f)      t2 = appendTree2 t1 (node3 a b c) (node3 d e f) t2
addDigits3 t1 (One a)        b c d (Three e f g)  t2 = appendTree3 t1 (node3 a b c) (node2 d e) (node2 f g) t2
addDigits3 t1 (One a)        b c d (Four e f g h) t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node2 g h) t2
addDigits3 t1 (Two a b)      c d e (One f)        t2 = appendTree2 t1 (node3 a b c) (node3 d e f) t2
addDigits3 t1 (Two a b)      c d e (Two f g)      t2 = appendTree3 t1 (node3 a b c) (node2 d e) (node2 f g) t2
addDigits3 t1 (Two a b)      c d e (Three f g h)  t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node2 g h) t2
addDigits3 t1 (Two a b)      c d e (Four f g h i) t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node3 g h i) t2
addDigits3 t1 (Three a b c)  d e f (One g)        t2 = appendTree3 t1 (node3 a b c) (node2 d e) (node2 f g) t2
addDigits3 t1 (Three a b c)  d e f (Two g h)      t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node2 g h) t2
addDigits3 t1 (Three a b c)  d e f (Three g h i)  t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node3 g h i) t2
addDigits3 t1 (Three a b c)  d e f (Four g h i j) t2 = appendTree4 t1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) t2
addDigits3 t1 (Four a b c d) e f g (One h)        t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node2 g h) t2
addDigits3 t1 (Four a b c d) e f g (Two h i)      t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node3 g h i) t2
addDigits3 t1 (Four a b c d) e f g (Three h i j)  t2 = appendTree4 t1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) t2
addDigits3 t1 (Four a b c d) e f g (Four h i j k) t2 = appendTree4 t1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) t2

addDigits4 t1 (One a)        b c d e (One f)        t2 = appendTree2 t1 (node3 a b c) (node3 d e f) t2
addDigits4 t1 (One a)        b c d e (Two f g)      t2 = appendTree3 t1 (node3 a b c) (node2 d e) (node2 f g) t2
addDigits4 t1 (One a)        b c d e (Three f g h)  t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node2 g h) t2
addDigits4 t1 (One a)        b c d e (Four f g h i) t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node3 g h i) t2
addDigits4 t1 (Two a b)      c d e f (One g)        t2 = appendTree3 t1 (node3 a b c) (node2 d e) (node2 f g) t2
addDigits4 t1 (Two a b)      c d e f (Two g h)      t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node2 g h) t2
addDigits4 t1 (Two a b)      c d e f (Three g h i)  t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node3 g h i) t2
addDigits4 t1 (Two a b)      c d e f (Four g h i j) t2 = appendTree4 t1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) t2
addDigits4 t1 (Three a b c)  d e f g (One h)        t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node2 g h) t2
addDigits4 t1 (Three a b c)  d e f g (Two h i)      t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node3 g h i) t2
addDigits4 t1 (Three a b c)  d e f g (Three h i j)  t2 = appendTree4 t1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) t2
addDigits4 t1 (Three a b c)  d e f g (Four h i j k) t2 = appendTree4 t1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) t2
addDigits4 t1 (Four a b c d) e f g h (One i)        t2 = appendTree3 t1 (node3 a b c) (node3 d e f) (node3 g h i) t2
addDigits4 t1 (Four a b c d) e f g h (Two i j)      t2 = appendTree4 t1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) t2
addDigits4 t1 (Four a b c d) e f g h (Three i j k)  t2 = appendTree4 t1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) t2
addDigits4 t1 (Four a b c d) e f g h (Four i j k l) t2 = appendTree4 t1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) t2

Split : Type -> Type -> Type
Split t a = (t, a, t)

data SearchResult : Type -> Type where
  Position : PosMap a -> a -> PosMap a -> SearchResult a
  OnLeft : SearchResult a
  OnRight : SearchResult a
  Nowhere : SearchResult a

searchDigit : MeasureRM a => (Interval -> Interval -> Bool) -> Interval -> Digit a -> Interval -> Split (Maybe (Digit a)) a
searchDigit p vl (One a) vr = (Nothing, a, Nothing)
searchDigit p vl (Two a b) vr =
  let va = vl <+> cast (measureRM a)
      vb = cast (measureRM b) <+> vr in
      if p va vb
         then (Nothing, a, Just (One b))
         else (Just (One a), b, Nothing)
searchDigit p vl (Three a b c) vr =
  let va  = vl <+> cast (measureRM a)
      vab = va <+> cast (measureRM b)
      vc  = cast (measureRM c) <+> vr
      vbc = cast (measureRM b) <+> vc in
      if p va vbc
         then (Nothing, a, Just (Two b c))
         else if p vab vc
                 then (Just (One a), b, Just (One c))
                 else (Just (Two a b), c, Nothing)
searchDigit p vl (Four a b c d) vr =
  let va   = vl <+> cast (measureRM a)
      vab  = va <+> cast (measureRM b)
      vabc = vab <+> cast (measureRM c)
      vd   = cast (measureRM d) <+> vr
      vcd  = cast (measureRM c) <+> vd
      vbcd = cast (measureRM b) <+> vcd in
      if p va vbcd
         then (Nothing, a, Just (Three b c d))
         else if p vab vcd
                 then (Just (One a), b, Just (Two c d))
                 else if p vabc vd
                         then (Just (Two a b), c, Just (One d))
                         else (Just (Three a b c), d, Nothing)

deepl : MeasureRM a => Maybe (Digit a) -> PosMap (Node a) -> Digit a -> PosMap a
deepl Nothing m sf = rotl m sf
deepl (Just pr) m sf = deep pr m sf

deepr : MeasureRM a => Digit a -> PosMap (Node a) -> Maybe (Digit a) -> PosMap a
deepr pr m Nothing = rotr pr m
deepr pr m (Just sf) = deep pr m sf

searchNode : MeasureRM a => (Interval -> Interval -> Bool) -> Interval -> Node a -> Interval -> Split (Maybe (Digit a)) a
searchNode p vl x vr = searchDigit p vl (nodeToDigit x) vr

searchTree : MeasureRM a => (Interval -> Interval -> Bool) -> Interval -> PosMap a -> Interval -> Maybe (Split (PosMap a) a)
searchTree p vl Empty vr = Nothing
searchTree p vl (Single x) vr = Just (Empty, x, Empty)
searchTree p vl (Deep _ pr m sf) vr =
  let vm   = measureTree m
      vsr  = cast (measureRM sf) <+> vr
      vmsr = vm <+> vsr
      vlp  = vl <+> cast (measureRM pr)
      vlpm = vlp <+> vm in
      if p vlp vmsr
         then let (l, x, r) = searchDigit p vl pr vmsr in
                  Just (maybe Empty digitToTree l, x, deepl r m sf)
         else if p vlpm vsr
                 then do (ml, xs, mr) <- searchTree p vlp m vsr
                         let (l, x, r) = searchNode p (vlp <+> measureTree ml) xs (measureTree mr <+> vsr)
                         Just (deepr pr ml l, x, deepl r mr sf)
                 else let (l, x, r) = searchDigit p vlpm sf vr in
                          Just (deepr pr m l, x, maybe Empty digitToTree r)

search' : MeasureRM a => (Interval -> Interval -> Bool) -> PosMap a -> SearchResult a
search' p t =
  let vt     = measureTree t
      pLeft  = p neutral vt
      pRight = p vt neutral in
      case (pLeft, pRight) of
           (True,  True)  => OnLeft
           (False, True)  => case searchTree p neutral t neutral of
                                  Just (l, x, r) => Position l x r
                                  Nothing => Nowhere
           (False, False) => OnRight
           (True,  False) => Nowhere

split : MeasureRM a => (Interval -> Bool) -> PosMap a -> (PosMap a, PosMap a)
split p Empty = (Empty, Empty)
split p xs =
  case searchTree (\a, _ => p a) neutral xs neutral of
       Just (l, x, r) => if p (measureTree xs)
                            then (l, x <| r)
                            else (xs, Empty)
       Nothing => (xs, Empty)

(++) : MeasureRM a => PosMap a -> PosMap a -> PosMap a
xs ++ ys = appendTree0 xs ys

export
map : MeasureRM b => (a -> b) -> PosMap a -> PosMap b
map f Empty = Empty
map f (Single x) = Single (f x)
map f (Deep _ pr t sf) = deep (map f pr) (map (map f) t) (map f sf)

export
traverse : (Applicative f, MeasureRM b) => (a -> f b) -> PosMap a -> f (PosMap b)
traverse f Empty = [| Empty |]
traverse f (Single x) = [| Single (f x) |]
traverse f (Deep _ pr t sf) = [| deep (traverse f pr) (traverse (traverse f) t) (traverse f sf) |]

export
takeUntil : MeasureRM a => (Interval -> Bool) -> PosMap a -> PosMap a
takeUntil p = fst . split p

export
dropUntil : MeasureRM a => (Interval -> Bool) -> PosMap a -> PosMap a
dropUntil p = snd . split p

export
Show a => Show (PosMap a) where
  showPrec p xs = showCon p "fromList" $ showArg (foldr (::) [] xs)

larger : FileRange -> Interval -> Bool
larger i (MkInterval (MkRange k _)) = k >= i
larger i NoInterval = False

larger' : FileRange -> Interval -> Bool
larger' i (MkInterval (MkRange k _)) = k > i
larger' i NoInterval = False

||| Inserts a new element in the map, in lexicographical order.
export
insert : Measure a => a -> PosMap a -> PosMap a
insert v m = let (l, r) = split (larger (measure v)) m in l ++ (v <| r)

||| Builds a new map from a list of measurable elements, inserting in
||| lexicographical order.
export
fromList : Measure a => List a -> PosMap a
fromList = foldr insert empty

merge1 : Measure a => PosMap a -> PosMap a -> PosMap a
merge2 : Measure a => PosMap a -> PosMap a -> PosMap a

merge1 xs ys =
  case viewl xs of
       EmptyL => ys
       a <: as' => let (l, r) = split (larger (measure a)) ys in
                       l ++ (a <| assert_total (merge2 as' r))

merge2 xs ys =
  case viewl ys of
       EmptyL => xs
       b <: bs' => let (l, r) = split (larger' (measure b)) xs in
                       l ++ (b <| assert_total (merge1 r bs'))

||| Merges two interval maps.
export
union : Measure a => PosMap a -> PosMap a -> PosMap a
union xs ys = merge1 xs ys

atleast : FilePos -> Interval -> Bool
atleast k (MkInterval (MkRange _ high)) = k <= high
atleast k NoInterval = False

greater : FilePos -> Interval -> Bool
greater k (MkInterval (MkRange low _)) = fst low > k
greater k NoInterval = False

-- Finds all the interval that overlaps with the given interval.
-- takeUntil selects all the intervals within the given upper bound,
-- however the remaining interval are not necessarily adjacent in
-- the sequence, thus it drops elements until the next intersecting
-- interval with dropUntil.
inRange : MeasureRM a => FilePos -> FilePos -> PosMap a -> List a
inRange low high t = matches (takeUntil (greater high) t)
  where matches : PosMap a -> List a
        matches xs = case viewl (dropUntil (atleast low) xs) of
                          EmptyL => []
                          x <: xs' => x :: assert_total (matches xs')

||| Returns all the interval that contains the given point.
export
searchPos : MeasureRM a => FilePos -> PosMap a -> List a
searchPos p = inRange p p

||| Returns all the intervals that intersect the given interval.
export
intersections : MeasureRM a => FileRange -> PosMap a -> List a
intersections i = inRange (fst i) (snd i)

||| Returns all the intervals that contain the given interval.
export
dominators : MeasureRM a => FileRange -> PosMap a -> List a
dominators i = inRange (snd i) (fst i)

||| Returns the extreme boundaries of the map, if non empty.
export
bounds : Measure a => PosMap a -> Maybe FileRange
bounds t =
  case measureTree t of
       NoInterval => Nothing
       MkInterval (MkRange _ high) =>
         case viewl t of
              EmptyL => Nothing
              x <: _ => Just (fst (measure x), high)

public export
Measure NonEmptyFC where
  measure = snd

public export
Measure (NonEmptyFC, a) where
  measure = measure . fst
