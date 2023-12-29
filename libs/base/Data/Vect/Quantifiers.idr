module Data.Vect.Quantifiers

import Data.DPair
import Data.Vect

%default total

------------------------------------------------------------------------
-- Types and basic properties

namespace Any
  ||| A proof that some element of a vector satisfies some property
  |||
  ||| @ p the property to be satsified
  public export
  data Any : (0 p : a -> Type) -> Vect n a -> Type where
    ||| A proof that the satisfying element is the first one in the `Vect`
    Here  : {0 xs : Vect n a} -> p x -> Any p (x :: xs)
    ||| A proof that the satsifying element is in the tail of the `Vect`
    There : {0 xs : Vect n a} -> Any p xs -> Any p (x :: xs)

  export
  implementation Uninhabited (Any p Nil) where
    uninhabited (Here _) impossible
    uninhabited (There _) impossible

  export
  implementation {0 p : a -> Type} -> Uninhabited (p x) => Uninhabited (Any p xs) => Uninhabited (Any p $ x::xs) where
    uninhabited (Here y) = uninhabited y
    uninhabited (There y) = uninhabited y

  ||| Eliminator for `Any`
  public export
  anyElim : {0 xs : Vect n a} -> {0 p : a -> Type} -> (Any p xs -> b) -> (p x -> b) -> Any p (x :: xs) -> b
  anyElim _ f (Here p) = f p
  anyElim f _ (There p) = f p

  ||| Given a decision procedure for a property, determine if an element of a
  ||| vector satisfies it.
  |||
  ||| @ p the property to be satisfied
  ||| @ dec the decision procedure
  ||| @ xs the vector to examine
  public export
  any : (dec : (x : a) -> Dec (p x)) -> (xs : Vect n a) -> Dec (Any p xs)
  any _ Nil = No uninhabited
  any p (x::xs) with (p x)
    any p (x::xs) | Yes prf = Yes (Here prf)
    any p (x::xs) | No prf =
      case any p xs of
        Yes prf' => Yes (There prf')
        No prf' => No (anyElim prf' prf)

  export
  mapProperty : (f : forall x. p x -> q x) -> Any p l -> Any q l
  mapProperty f (Here p)  = Here (f p)
  mapProperty f (There p) = There (mapProperty f p)

  export
  toExists : Any p xs -> Exists p
  toExists (Here prf)  = Evidence _ prf
  toExists (There prf) = toExists prf

  ||| Get the bounded numeric position of the element satisfying the predicate
  public export
  anyToFin : {0 xs : Vect n a} -> Any p xs -> Fin n
  anyToFin (Here _) = FZ
  anyToFin (There later) = FS (anyToFin later)

  ||| `anyToFin`'s return type satisfies the predicate
  export
  anyToFinCorrect : {0 xs : Vect n a} ->
                    (witness : Any p xs) ->
                    p (anyToFin witness `index` xs)
  anyToFinCorrect (Here prf) = prf
  anyToFinCorrect (There later) = anyToFinCorrect later

namespace All
  ||| A proof that all elements of a vector satisfy a property. It is a list of
  ||| proofs, corresponding element-wise to the `Vect`.
  public export
  data All : (0 p : a -> Type) -> Vect n a -> Type where
    Nil  : All p Nil
    (::) : {0 xs : Vect n a} -> p x -> All p xs -> All p (x :: xs)

  ||| If there does not exist an element that satifies the property, then it is
  ||| the case that all elements do not satisfy.
  export
  negAnyAll : {xs : Vect n a} -> Not (Any p xs) -> All (Not . p) xs
  negAnyAll {xs=Nil} _ = Nil
  negAnyAll {xs=(x::xs)} f = (f . Here) :: negAnyAll (f . There)

  export
  notAllHere : {0 p : a -> Type} -> {xs : Vect n a} -> Not (p x) -> Not (All p (x :: xs))
  notAllHere _ Nil impossible
  notAllHere np (p :: _) = np p

  export
  notAllThere : {0 p : a -> Type} -> {xs : Vect n a} -> Not (All p xs) -> Not (All p (x :: xs))
  notAllThere _ Nil impossible
  notAllThere np (_ :: ps) = np ps

  ||| Given a decision procedure for a property, decide whether all elements of
  ||| a vector satisfy it.
  |||
  ||| @ p the property
  ||| @ dec the decision procedure
  ||| @ xs the vector to examine
  public export
  all : (dec : (x : a) -> Dec (p x)) -> (xs : Vect n a) -> Dec (All p xs)
  all _ Nil = Yes Nil
  all d (x::xs) with (d x)
    all d (x::xs) | No prf = No (notAllHere prf)
    all d (x::xs) | Yes prf =
      case all d xs of
        Yes prf' => Yes (prf :: prf')
        No prf' => No (notAllThere prf')

  export
  Either (Uninhabited $ p x) (Uninhabited $ All p xs) => Uninhabited (All p $ x::xs) where
    uninhabited @{Left  _} (px::pxs) = uninhabited px
    uninhabited @{Right _} (px::pxs) = uninhabited pxs

  export
  mapProperty : (f : forall x. p x -> q x) -> All p l -> All q l
  mapProperty f [] = []
  mapProperty f (p::pl) = f p :: mapProperty f pl

  ||| A variant of `mapProperty` that also allows accessing
  ||| the values of `xs` that the corresponding `ps` prove `p` about.
  export
  mapPropertyRelevant : {xs : Vect n a} ->
                        (f : (x : a) -> p x -> q x) ->
                        (ps : All p xs) ->
                        All q xs
  mapPropertyRelevant f [] = []
  mapPropertyRelevant f (p :: ps) = f _ p :: mapPropertyRelevant f ps

  public export
  imapProperty : {0 a : Type}
              -> {0 p,q : a -> Type}
              -> (0 i : a -> Type)
              -> (f : {0 x : a} -> i x => p x -> q x)
              -> {0 as : Vect n a}
              -> All i as => All p as -> All q as
  imapProperty _ _              []      = []
  imapProperty i f @{ix :: ixs} (x::xs) = f @{ix} x :: imapProperty i f @{ixs} xs

  ||| If `All` witnesses a property that does not depend on the vector `xs`
  ||| it's indexed by, then it is really a `Vect`.
  public export
  forget : All (const p) {n} xs -> Vect n p
  forget []      = []
  forget (x::xs) = x :: forget xs

  ||| Any `Vect` can be lifted to become an `All`
  ||| witnessing the presence of elements of the `Vect`'s type.
  public export
  remember : (xs : Vect n ty) -> All (const ty) xs
  remember [] = []
  remember (x :: xs) = x :: remember xs

  export
  forgetRememberId : (xs : Vect n ty) -> forget (remember xs) = xs
  forgetRememberId [] = Refl
  forgetRememberId (x :: xs) = cong (x ::) (forgetRememberId xs)

  public export
  castAllConst : {0 xs, ys : Vect n a} -> All (const ty) xs -> All (const ty) ys
  castAllConst [] = rewrite invertVectZ ys in []
  castAllConst (x :: xs) = rewrite invertVectS ys in x :: castAllConst xs

  export
  rememberForgetId : (vs : All (const ty) xs) ->
    castAllConst (remember (forget vs)) === vs
  rememberForgetId [] = Refl
  rememberForgetId (x :: xs) = cong (x ::) (rememberForgetId xs)

  export
  zipPropertyWith : (f : {0 x : a} -> p x -> q x -> r x) ->
                    All p xs -> All q xs -> All r xs
  zipPropertyWith f [] [] = []
  zipPropertyWith f (px :: pxs) (qx :: qxs)
    = f px qx :: zipPropertyWith f pxs qxs

  ||| A `Traversable`'s `traverse` for `All`,
  ||| for traversals that don't care about the values of the associated `Vect`.
  export
  traverseProperty : Applicative f =>
                     {0 xs : Vect n a} ->
                     (forall x. p x -> f (q x)) ->
                     All p xs ->
                     f (All q xs)
  traverseProperty f [] = pure []
  traverseProperty f (x :: xs) = [| f x :: traverseProperty f xs |]

  ||| A `Traversable`'s `traverse` for `All`,
  ||| in case the elements of the `Vect` that the `All` is proving `p` about are also needed.
  export
  traversePropertyRelevant : Applicative f =>
                             {xs : Vect n a} ->
                             ((x : a) -> p x -> f (q x)) ->
                             All p xs ->
                             f (All q xs)
  traversePropertyRelevant f [] = pure []
  traversePropertyRelevant f (x :: xs) = [| f _ x :: traversePropertyRelevant f xs |]

  public export
  tabulate : {n : _} ->
             {0 xs : Vect n _} ->
             (f : (ix : Fin n) -> p (ix `index` xs)) ->
             All p {n} xs
  tabulate {xs = []} f = []
  tabulate {xs = _ :: _} f = f FZ :: tabulate (\ix => f (FS ix))

  public export
  (++) : (axs : All p xs) -> (ays : All p ys) -> All p (xs ++ ys)
  [] ++ ays = ays
  (ax :: axs) ++ ays = ax :: (axs ++ ays)

  export
  All (Show . p) xs => Show (All p xs) where
    show pxs = "[" ++ show' "" pxs ++ "]"
      where
        show' : String -> All (Show . p) xs' => All p xs' -> String
        show' acc @{[]} [] = acc
        show' acc @{[_]} [px] = acc ++ show px
        show' acc @{_ :: _} (px :: pxs) = show' (acc ++ show px ++ ", ") pxs

  export
  All (Eq . p) xs => Eq (All p xs) where
    (==)           [] []             = True
    (==) @{_ :: _} (h1::t1) (h2::t2) = h1 == h2 && t1 == t2

  %hint
  allEq : All (Ord . p) xs => All (Eq . p) xs
  allEq @{[]}     = []
  allEq @{_ :: _} = %search :: allEq

  export
  All (Ord . p) xs => Ord (All p xs) where
    compare            [] []            = EQ
    compare @{_ :: _} (h1::t1) (h2::t2) = case compare h1 h2 of
      EQ => compare t1 t2
      o  => o

  export
  All (Semigroup . p) xs => Semigroup (All p xs) where
    (<+>)           [] [] = []
    (<+>) @{_ :: _} (h1::t1) (h2::t2) = (h1 <+> h2) :: (t1 <+> t2)

  %hint
  allSemigroup : All (Monoid . p) xs => All (Semigroup . p) xs
  allSemigroup @{[]}     = []
  allSemigroup @{_ :: _} = %search :: allSemigroup

  export
  All (Monoid . p) xs => Monoid (All p xs) where
    neutral @{[]}   = []
    neutral @{_::_} = neutral :: neutral

  ||| A heterogeneous vector of arbitrary types
  public export
  HVect : Vect n Type -> Type
  HVect = All id

  ||| Take the first element.
  export
  head : All p (x :: xs) -> p x
  head (y :: _) = y

  ||| Take all but the first element.
  export
  tail : All p (x :: xs) -> All p xs
  tail (_ :: ys) = ys

  ||| Drop the first n elements given knowledge that
  ||| there are at least n elements available.
  export
  drop : {0 m : _} -> (n : Nat) -> {0 xs : Vect (n + m) a} -> All p xs -> All p (the (Vect m a) (Vect.drop n xs))
  drop 0 ys = ys
  drop (S k) (y :: ys) = drop k ys

  ||| Drop up to the first l elements, stopping early
  ||| if all elements have been dropped.
  export
  drop' : {0 k : _} -> {0 xs : Vect k _} -> (l : Nat) -> All p xs -> All p (Vect.drop' l xs)
  drop' 0 ys = rewrite minusZeroRight k in ys
  drop' (S k) [] = []
  drop' (S k) (y :: ys) = drop' k ys
