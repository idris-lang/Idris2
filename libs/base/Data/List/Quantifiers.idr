module Data.List.Quantifiers

import Data.DPair

import Data.List.Elem

%default total

------------------------------------------------------------------------
-- Types and basic properties

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

  export
  Uninhabited (Any p Nil) where
    uninhabited (Here _) impossible
    uninhabited (There _) impossible

  export
  {0 p : a -> Type} -> Uninhabited (p x) => Uninhabited (Any p xs) => Uninhabited (Any p $ x::xs) where
    uninhabited (Here y) = uninhabited y
    uninhabited (There y) = uninhabited y

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
  export
  toExists : Any p xs -> Exists p
  toExists (Here prf) = Evidence _ prf
  toExists (There prf) = toExists prf

namespace All

  ||| A proof that all elements of a list satisfy a property. It is a list of
  ||| proofs, corresponding element-wise to the `List`.
  public export
  data All : (0 p : a -> Type) -> List a -> Type where
    Nil  : All p Nil
    (::) : {0 xs : List a} -> p x -> All p xs -> All p (x :: xs)

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
  imapProperty : (0 i : Type -> Type)
              -> (f : {0 a : Type} -> i a => p a -> q a)
              -> {0 types : List Type}
              -> All i types => All p types -> All q types
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
  All Show (map p xs) => Show (All p xs) where
    show pxs = "[" ++ show' "" pxs ++ "]"
      where
        show' : String -> All Show (map p xs') => All p xs' -> String
        show' acc @{[]} [] = acc
        show' acc @{[_]} [px] = acc ++ show px
        show' acc @{_ :: _} (px :: pxs) = show' (acc ++ show px ++ ", ") pxs

  ||| A heterogeneous list of arbitrary types
  public export
  HList : List Type -> Type
  HList = All id

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

||| Given a proof of membership for some element, extract the property proof for it
public export
indexAll : Elem x xs -> All p xs -> p x
indexAll  Here     (p::_  ) = p
indexAll (There e) ( _::ps) = indexAll e ps

--- Relations between listwise `All` and elementwise `Subset` ---

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
pushOutInInverse : (xs : List $ Subset a p) -> uncurry Quantifiers.pushIn (pullOut xs) = xs
pushOutInInverse [] = Refl
pushOutInInverse (Element x p :: xs) with (pushOutInInverse xs)
  pushOutInInverse (Element x p :: xs) | subprf with (pullOut xs)
    pushOutInInverse (Element x p :: xs) | subprf | Element ss ps = rewrite subprf in Refl

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
