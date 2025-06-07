module Data.List.Quantifiers

import Data.DPair
import Data.Fin
import Data.List
import Data.List.Elem

%default total

------------------------------------------------------------------------
-- Quantifier types

namespace Any

  ||| A proof that some element of a list satisfies some property
  |||
  ||| @ p the property to be satisfied
  public export
  data Any : (0 p : a -> Type) -> List a -> Type where
    ||| A proof that the satisfying element is the first one in the `List`
    Here  : {0 xs : List a} -> p x -> Any p (x :: xs)
    ||| A proof that the satisfying element is in the tail of the `List`
    There : {0 xs : List a} -> Any p xs -> Any p (x :: xs)

namespace All

  ||| A proof that all elements of a list satisfy a property. It is a list of
  ||| proofs, corresponding element-wise to the `List`.
  public export
  data All : (0 p : a -> Type) -> List a -> Type where
    Nil  : All p Nil
    (::) : {0 xs : List a} -> p x -> All p xs -> All p (x :: xs)

------------------------------------------------------------------------
-- Basic properties

namespace Any

  export
  All (Uninhabited . p) xs => Uninhabited (Any p xs) where
    uninhabited @{s::ss} (Here y)  = uninhabited y
    uninhabited @{s::ss} (There y) = uninhabited y

  ||| Modify the property given a pointwise function
  export
  mapProperty : (f : {0 x : a} -> p x -> q x) -> Any p l -> Any q l
  mapProperty f (Here p) = Here (f p)
  mapProperty f (There p) = There (mapProperty f p)

  ||| Given a decision procedure for a property, determine if an element of a
  ||| list satisfies it.
  |||
  ||| @ p the property to be satisfied
  ||| @ dec the decision procedure
  ||| @ xs the list to examine
  public export
  any : (dec : (x : a) -> Dec (p x)) -> (xs : List a) -> Dec (Any p xs)
  any _ Nil = No uninhabited
  any p (x::xs) with (p x)
    any p (x::xs) | Yes prf = Yes (Here prf)
    any p (x::xs) | No ctra =
      case any p xs of
        Yes prf' => Yes (There prf')
        No ctra' => No $ \case
          Here px => ctra px
          There pxs => ctra' pxs

  ||| Forget the membership proof
  public export
  toDPair : {xs : List a} -> Any p xs -> DPair a p
  toDPair (Here prf) = (_ ** prf)
  toDPair (There p)  = toDPair p

  ||| Forget the membership proof
  export
  toExists : Any p xs -> Exists p
  toExists (Here prf) = Evidence _ prf
  toExists (There prf) = toExists prf

  public export
  anyToFin : Any p xs -> Fin $ length xs
  anyToFin (Here _)      = FZ
  anyToFin (There later) = FS (anyToFin later)

  export
  anyToFinCorrect : (witness : Any p xs) -> p $ index' xs $ anyToFin witness
  anyToFinCorrect (Here prf) = prf
  anyToFinCorrect (There later) = anyToFinCorrect later

  public export
  anyToFinV : Any p xs -> (idx : Fin $ length xs ** p $ index' xs idx)
  anyToFinV $ Here x  = (FZ ** x)
  anyToFinV $ There x = let (idx ** v) = anyToFinV x in (FS idx ** v)

  public export
  pushOut : Functor p => Any (p . q) xs -> p $ Any q xs
  pushOut @{fp} (Here v)  = map @{fp} Here v
  pushOut @{fp} (There n) = map @{fp} There $ pushOut n

  export
  All (Show . p) xs => Show (Any p xs) where
    showPrec d @{s::ss} (Here x)  = showCon d "Here"  $ showArg x
    showPrec d @{s::ss} (There x) = showCon d "There" $ showArg x

  export
  All (Eq . p) xs => Eq (Any p xs) where
    (==) @{s::ss} (Here x)  (Here y)  = x == y
    (==) @{s::ss} (There x) (There y) = x == y
    (==) _ _ = False

namespace All

  Either (Uninhabited $ p x) (Uninhabited $ All p xs) => Uninhabited (All p $ x::xs) where
    uninhabited @{Left  _} (px::pxs) = uninhabited px
    uninhabited @{Right _} (px::pxs) = uninhabited pxs

  ||| Modify the property given a pointwise function
  export
  mapProperty : (f : {0 x : a} -> p x -> q x) -> All p l -> All q l
  mapProperty f [] = []
  mapProperty f (p::pl) = f p :: mapProperty f pl

  ||| Modify the property given a pointwise interface function
  public export
  imapProperty : {0 a : Type}
              -> {0 p,q : a -> Type}
              -> (0 i : a -> Type)
              -> (f : {0 x : a} -> i x => p x -> q x)
              -> {0 as : List a}
              -> All i as => All p as -> All q as
  imapProperty i f @{[]} [] = []
  imapProperty i f @{ix :: ixs} (x :: xs) = f @{ix} x :: imapProperty i f @{ixs} xs

  ||| Forget property source for a homogeneous collection of properties
  public export
  forget : All (const type) types -> List type
  forget [] = []
  forget (x :: xs) = x :: forget xs

  ||| Given a decision procedure for a property, decide whether all elements of
  ||| a list satisfy it.
  |||
  ||| @ p the property
  ||| @ dec the decision procedure
  ||| @ xs the list to examine
  public export
  all : (dec : (x : a) -> Dec (p x)) -> (xs : List a) -> Dec (All p xs)
  all _ Nil = Yes Nil
  all d (x::xs) with (d x)
    all d (x::xs) | No ctra = No $ \(p::_) => ctra p
    all d (x::xs) | Yes prf =
      case all d xs of
        Yes prf' => Yes (prf :: prf')
        No ctra' => No $ \(_::ps) => ctra' ps

  export
  zipPropertyWith : (f : {0 x : a} -> p x -> q x -> r x) ->
                    All p xs -> All q xs -> All r xs
  zipPropertyWith f [] [] = []
  zipPropertyWith f (px :: pxs) (qx :: qxs)
    = f px qx :: zipPropertyWith f pxs qxs

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

  ||| A heterogeneous list of arbitrary types
  public export
  HList : List Type -> Type
  HList = All id

  ||| Concatenate lists of proofs.
  public export
  (++) : All p xs -> All p ys -> All p (xs ++ ys)
  [] ++ pys = pys
  (px :: pxs) ++ pys = px :: (pxs ++ pys)

  ||| Take the first element.
  public export
  head : All p (x :: xs) -> p x
  head (y :: _) = y

  ||| Take all but the first element.
  public export
  tail : All p (x :: xs) -> All p xs
  tail (_ :: ys) = ys

  export
  splitAt : (xs : List a) -> All p (xs ++ ys) -> (All p xs, All p ys)
  splitAt [] pxs = ([], pxs)
  splitAt (_ :: xs) (px :: pxs) = mapFst (px ::) (splitAt xs pxs)

  export
  take : (xs : List a) -> All p (xs ++ ys) -> All p xs
  take xs pxs = fst (splitAt xs pxs)

  export
  drop : (xs : List a) -> All p (xs ++ ys) -> All p ys
  drop xs pxs = snd (splitAt xs pxs)

  export
  drop' : (l : Nat) -> All p xs -> All p (drop l xs)
  drop' Z     as      = as
  drop' (S k) []      = []
  drop' (S k) (a::as) = drop' k as

  ||| Push in the property from the list level with element level
  public export
  pushIn : (xs : List a) -> (0 _ : All p xs) -> List $ Subset a p
  pushIn []      []      = []
  pushIn (x::xs) (p::ps) = Element x p :: pushIn xs ps

  ||| Pull the elementwise property out to the list level
  public export
  pullOut : (xs : List $ Subset a p) -> Subset (List a) (All p)
  pullOut [] = Element [] []
  pullOut (Element x p :: xs) = let Element ss ps = pullOut xs in Element (x::ss) (p::ps)

  export
  pushInOutInverse : (xs : List a) -> (0 prf : All p xs) -> pullOut (pushIn xs prf) = Element xs prf
  pushInOutInverse [] [] = Refl
  pushInOutInverse (x::xs) (p::ps) = rewrite pushInOutInverse xs ps in Refl

  export
  pushOutInInverse : (xs : List $ Subset a p) -> uncurry All.pushIn (pullOut xs) = xs
  pushOutInInverse [] = Refl
  pushOutInInverse (Element x p :: xs) with (pushOutInInverse xs)
    pushOutInInverse (Element x p :: xs) | subprf with (pullOut xs)
      pushOutInInverse (Element x p :: xs) | subprf | Element ss ps = rewrite subprf in Refl

  ||| Given a proof of membership for some element, extract the property proof for it
  public export
  indexAll : Elem x xs -> All p xs -> p x
  indexAll  Here     (p::_  ) = p
  indexAll (There e) ( _::ps) = indexAll e ps

  ||| Given an index of an element, extract the property proof for it
  public export
  index : (idx : Fin $ length xs) -> All p xs -> p (index' xs idx)
  index FZ     (p::ps) = p
  index (FS i) (p::ps) = index i ps

  public export
  pushOut : Applicative p => All (p . q) xs -> p $ All q xs
  pushOut []      = pure []
  pushOut (x::xs) = [| x :: pushOut xs |]

------------------------------------------------------------------------
-- Relationship between all and any

||| If there does not exist an element that satifies the property, then it is
||| the case that all elements do not satisfy it.
export
negAnyAll : {xs : List a} -> Not (Any p xs) -> All (Not . p) xs
negAnyAll {xs=Nil}   _ = Nil
negAnyAll {xs=x::xs} f = (f . Here) :: negAnyAll (f . There)

||| If there exists an element that doesn't satify the property, then it is
||| not the case that all elements satisfy it.
export
anyNegAll : Any (Not . p) xs -> Not (All p xs)
anyNegAll (Here ctra) (p::_)  = ctra p
anyNegAll (There np)  (_::ps) = anyNegAll np ps

||| If none of the elements satisfy the property, then not any single one can.
export
allNegAny : All (Not . p) xs -> Not (Any p xs)
allNegAny [] p = absurd p
allNegAny (np :: npxs) (Here p) = absurd (np p)
allNegAny (np :: npxs) (There p) = allNegAny npxs p

public export
allAnies : All p xs -> List (Any p xs)
allAnies [] = []
allAnies (x::xs) = Here x :: map There (allAnies xs)

export
altAll : Alternative p => All (p . q) xs -> p $ Any q xs
altAll []      = empty
altAll (a::as) = Here <$> a <|> There <$> altAll as

------------------------------------------------------------------------
-- Partitioning lists according to All

||| Two lists, `xs` and `ys`, whose elements are interleaved in the list `xys`.
public export
data Interleaving : (xs, ys, xys : List a) -> Type where
  Nil   : Interleaving [] [] []
  Left  : Interleaving xs ys xys -> Interleaving (x :: xs) ys (x :: xys)
  Right : Interleaving xs ys xys -> Interleaving xs (y :: ys) (y :: xys)

||| A record for storing the result of splitting a list `xys` according to some
||| property `p`.
||| The `prfs` and `contras` are related to the original list (`xys`) via
||| `Interleaving`.
|||
||| @ xys the list which has been split
||| @ p   the property used for the split
public export
record Split {a : Type} (p : a -> Type) (xys : List a) where
  constructor MkSplit
  {ayes, naws : List a}
  {auto interleaving : Interleaving ayes naws xys}
  ||| A proof that all elements in `ayes` satisfies the property used for the
  ||| split.
  prfs    : All p ayes
  ||| A proof that all elements in `naws` do not satisfy the property used for
  ||| the split.
  contras : All (Not . p) naws

||| Split the list according to the given decidable property, putting the
||| resulting proofs and contras in an accumulator.
|||
||| @ dec a function which returns a decidable property
||| @ xs  a list of elements to split
||| @ a   the accumulator
public export
splitOnto :  (dec : (x : a) -> Dec (p x))
          -> (xs : List a)
          -> (a : Split p acc)
          -> Split p (reverseOnto acc xs)
splitOnto dec [] a = a
splitOnto dec (x :: xs) (MkSplit prfs contras) =
  case dec x of
       (Yes prf) => splitOnto dec xs (MkSplit (prf :: prfs) contras)
       (No contra) => splitOnto dec xs (MkSplit prfs (contra :: contras))

||| Split the list according to the given decidable property, starting with an
||| empty accumulator.
||| Use `splitOnto` if you want to specify the accumulator.
|||
||| @ dec a function which returns a decidable property
||| @ xs  a list of elements to split
||| @ a   the accumulator
public export
split :  (dec : (x : a) -> Dec (p x))
      -> (xs : List a)
      -> Split p (reverse xs)
split dec xs = splitOnto dec xs (MkSplit [] [])

||| If any `a` either satisfies p or q then given a List of as,
||| either all values satisfy p
||| or at least one of them sastifies q
public export
decide : ((x : a) -> Either (p x) (q x)) ->
         (xs : List a) -> Either (All p xs) (Any q xs)
decide dec [] = Left []
decide dec (x :: xs) = case dec x of
  Left px => case decide dec xs of
    Left pxs => Left (px :: pxs)
    Right pxs => Right (There pxs)
  Right px => Right (Here px)
