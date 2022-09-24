||| A Reversed List
module Data.SnocList

import Data.List
import Data.Fin

%default total

public export
Cast (SnocList a) (List a) where
  cast sx = sx <>> []

public export
Cast (List a) (SnocList a) where
  cast xs = Lin <>< xs

%transform "fastConcat" concat {t = SnocList} {a = String} = fastConcat . cast

||| Transform to a list but keeping the contents in the spine order (term depth).
public export
asList : SnocList type -> List type
asList = (reverse . cast)

export
Uninhabited (Lin = x :< xs) where
  uninhabited Refl impossible

export
Uninhabited (x :< xs = Lin) where
  uninhabited Refl impossible

||| True iff input is Lin
public export
isLin : SnocList a -> Bool
isLin Lin = True
isLin (sx :< x) = False

||| True iff input is (:<)
public export
isSnoc : SnocList a -> Bool
isSnoc Lin     = False
isSnoc (sx :< x) = True

||| Given a predicate and a snoclist, returns a tuple consisting of the longest
||| prefix of the snoclist whose elements satisfy the predicate, and the rest of the
||| snoclist.
public export
spanBy : (a -> Maybe b) -> SnocList a -> (SnocList a, SnocList b)
spanBy p [<] = ([<], [<])
spanBy p (xs :< x) = case p x of
  Just b =>
    let (as, bs) = spanBy p xs in
    (as, bs :< b)
  Nothing => (xs :< x, [<])

export
Show a => Show (SnocList a) where
  show xs = concat ("[< " :: intersperse ", " (show' [] xs) ++ ["]"])
    where
      show' : List String -> SnocList a -> List String
      show' acc Lin       = acc
      show' acc (xs :< x) = show' (show x :: acc) xs

public export
Functor SnocList where
  map f Lin = Lin
  map f (sx :< x) = (map f sx) :< (f x)

public export
Semigroup (SnocList a) where
  (<+>) = (++)

public export
Monoid (SnocList a) where
  neutral = Lin

public export
Foldable SnocList where
  foldr f z = foldr f z . (<>> [])

  foldl f z Lin = z
  foldl f z (xs :< x) = f (foldl f z xs) x

  null Lin      = True
  null (_ :< _) = False

  toList = (<>> [])

  foldMap f = foldl (\xs, x => xs <+> f x) neutral

public export
Applicative SnocList where
  pure = (:<) Lin
  fs <*> xs = concatMap (flip map xs) fs

public export
Monad SnocList where
  xs >>= k = concatMap k xs

public export
Traversable SnocList where
  traverse _ Lin = pure Lin
  traverse f (xs :< x) = [| traverse f xs :< f x |]

public export
Alternative SnocList where
  empty = Lin
  xs <|> ys = xs ++ ys

-- Why can't we just use an implementation here?!
export %hint
SnocBiinjective : Biinjective (:<)
SnocBiinjective = MkBiinjective $ \case Refl => (Refl, Refl)

||| Find the rightmost element of the snoc-list that satisfies the predicate.
public export
find : (a -> Bool) -> SnocList a -> Maybe a
find p Lin = Nothing
find p (xs :< x) = if p x then Just x else find p xs

||| Satisfiable if `k` is a valid index into `xs`.
|||
||| @ k  the potential index
||| @ xs the snoc-list into which k may be an index
public export
data InBounds : (k : Nat) -> (xs : SnocList a) -> Type where
    ||| Z is a valid index into any cons cell
    InFirst : InBounds Z (xs :< x)
    ||| Valid indices can be extended
    InLater : InBounds k xs -> InBounds (S k) (xs :< x)

||| Find the index (counting from right) of the rightmost element (if exists) of a
||| snoc-list that satisfies the given test, else `Nothing`.
public export
findIndex : (a -> Bool) -> (xs : SnocList a) -> Maybe $ Fin (length xs)
findIndex _ Lin = Nothing
findIndex p (xs :< x) = if p x
  then Just FZ
  else FS <$> findIndex p xs

------------------
--- Properties ---
------------------

--- Usual snoc-list append (++) ---

export
appendAssociative : (l, c, r : SnocList a) -> l ++ (c ++ r) = (l ++ c) ++ r
appendAssociative l c [<]       = Refl
appendAssociative l c (sx :< _) = rewrite appendAssociative l c sx in Refl

export
appendLinLeftNeutral : (sx : SnocList a) -> [<] ++ sx = sx
appendLinLeftNeutral [<]       = Refl
appendLinLeftNeutral (sx :< _) = rewrite appendLinLeftNeutral sx in Refl

--- Fish (<><) and chips (<>>) appends ---

export
fishAsSnocAppend : (xs : SnocList a) -> (ys : List a) -> xs <>< ys = xs ++ cast ys
fishAsSnocAppend xs []        = Refl
fishAsSnocAppend xs (y :: ys) = do
  rewrite fishAsSnocAppend (xs :< y) ys
  rewrite fishAsSnocAppend [<y] ys
  rewrite appendAssociative xs [<y] (cast ys)
  Refl

export
chipsAsListAppend : (xs : SnocList a) -> (ys : List a) -> xs <>> ys = cast xs ++ ys
chipsAsListAppend [<]       ys = Refl
chipsAsListAppend (sx :< x) ys = do
  rewrite chipsAsListAppend sx (x :: ys)
  rewrite chipsAsListAppend sx [x]
  rewrite sym $ appendAssociative (cast sx) [x] ys
  Refl

--- More on append ---

export
toListAppend : (sx, sy : SnocList a) -> toList (sx ++ sy) = toList sx ++ toList sy
toListAppend sx [<] = rewrite appendNilRightNeutral $ toList sx in Refl
toListAppend sx (sy :< y) = do
  rewrite chipsAsListAppend sy [y]
  rewrite appendAssociative (cast sx) (cast sy) [y]
  rewrite chipsAsListAppend (sx ++ sy) [y]
  rewrite toListAppend sx sy
  Refl

export
castListAppend : (xs, ys : List a) -> cast {to=SnocList a} (xs ++ ys) === cast xs ++ cast ys
castListAppend []      ys = rewrite appendLinLeftNeutral $ [<] <>< ys in Refl
castListAppend (x::xs) ys = do
  rewrite fishAsSnocAppend [<x] (xs ++ ys)
  rewrite castListAppend xs ys
  rewrite appendAssociative [<x] (cast xs) (cast ys)
  rewrite sym $ fishAsSnocAppend [<x] xs
  Refl

--- Pure casts (including `toList`)

export
castToList : (sx : SnocList a) -> cast (toList sx) === sx
castToList [<]       = Refl
castToList (sx :< x) = do
  rewrite chipsAsListAppend sx [x]
  rewrite castListAppend (cast sx) [x]
  rewrite castToList sx
  Refl

export
toListCast : (xs : List a) -> toList (cast {to=SnocList a} xs) === xs
toListCast []      = Refl
toListCast (x::xs) = do
  rewrite fishAsSnocAppend [<x] xs
  rewrite toListAppend [<x] (cast xs)
  rewrite toListCast xs
  Refl

||| Append an element to the head of a snoc-list.
||| Note: Traverses the snoc-list, linear time complexity
public export
cons : a -> SnocList a -> SnocList a
cons x sx = [< x] ++ sx

--- Folds ---

export
foldAppend : (f : acc -> a -> acc) -> (init : acc) -> (sx, sy : SnocList a) -> foldl f init (sx ++ sy) = foldl f (foldl f init sx) sy
foldAppend f init sx [<]       = Refl
foldAppend f init sx (sy :< x) = rewrite foldAppend f init sx sy in Refl

export
snocFoldlAsListFoldl : (f : acc -> a -> acc) -> (init : acc) -> (xs : SnocList a) -> foldl f init xs = foldl f init (toList xs)
snocFoldlAsListFoldl f init [<]       = Refl
snocFoldlAsListFoldl f init (sx :< x) = do
  rewrite chipsAsListAppend sx [x]
  rewrite snocFoldlAsListFoldl f init sx
  rewrite foldlAppend f init (cast sx) [x]
  Refl

--- Filtering ---

export
filterAppend : (f : a -> Bool) -> (sx, sy : SnocList a) -> filter f (sx ++ sy) = filter f sx ++ filter f sy
filterAppend f sx [<]       = Refl
filterAppend f sx (sy :< x) with (f x)
  _ | False = filterAppend f sx sy
  _ | True  = rewrite filterAppend f sx sy in Refl

export
toListFilter : (f : a -> Bool) -> (sx : SnocList a) -> toList (filter f sx) = filter f (toList sx)
toListFilter f [<]       = Refl
toListFilter f (sx :< x) = do
  rewrite chipsAsListAppend sx [x]
  rewrite filterAppend f (cast sx) [x]
  rewrite filterStepLemma
  rewrite toListFilter f sx
  Refl
  where
    filterStepLemma : toList (filter f (sx :< x)) = toList (filter f sx) ++ filter f [x]
    filterStepLemma with (f x)
      _ | False = rewrite appendNilRightNeutral $ toList $ filter f sx in Refl
      _ | True  = rewrite chipsAsListAppend (filter f sx) [x] in Refl

export
filterCast : (f : a -> Bool) -> (xs : List a) -> filter f (cast {to=SnocList a} xs) = cast (filter f xs)
filterCast f []      = Refl
filterCast f (x::xs) = do
  rewrite fishAsSnocAppend [<x] xs
  rewrite filterAppend f [<x] (cast xs)
  rewrite filterStepLemma
  rewrite filterCast f xs
  Refl
  where
    filterStepLemma : cast (filter f (x::xs)) = filter f [<x] ++ cast (filter f xs)
    filterStepLemma with (f x)
      _ | False = rewrite appendLinLeftNeutral $ [<] <>< filter f xs in Refl
      _ | True  = rewrite fishAsSnocAppend [<x] (filter f xs) in Refl

--- Functor map ---

export
mapFusion : (g : b -> c) -> (f : a -> b) -> (sx : SnocList a) -> map g (map f sx) = map (g . f) sx
mapFusion g f [<]       = Refl
mapFusion g f (sx :< x) = rewrite mapFusion g f sx in Refl

export
mapAppend : (f : a -> b) -> (sx, sy : SnocList a) -> map f (sx ++ sy) = map f sx ++ map f sy
mapAppend f sx [<]       = Refl
mapAppend f sx (sy :< x) = rewrite mapAppend f sx sy in Refl

export
toListMap : (f : a -> b) -> (sx : SnocList a) -> toList (map f sx) = map f (toList sx)
toListMap f [<]       = Refl
toListMap f (sx :< x) = do
  rewrite chipsAsListAppend (map f sx) [f x]
  rewrite chipsAsListAppend sx [x]
  rewrite mapAppend f (toList sx) [x]
  rewrite toListMap f sx
  Refl

export
mapCast : (f : a -> b) -> (xs : List a) -> map f (cast {to=SnocList a} xs) = cast (map f xs)
mapCast f []      = Refl
mapCast f (x::xs) = do
  rewrite fishAsSnocAppend [<f x] (map f xs)
  rewrite fishAsSnocAppend [<x] xs
  rewrite mapAppend f [<x] (cast xs)
  rewrite mapCast f xs
  Refl

--- mapMaybe ---

export
mapMaybeFusion : (g : b -> Maybe c) -> (f : a -> Maybe b) -> (sx : SnocList a) -> mapMaybe g (mapMaybe f sx) = mapMaybe (f >=> g) sx
mapMaybeFusion g f [<]       = Refl
mapMaybeFusion g f (sx :< x) with (f x)
  _ | Nothing = mapMaybeFusion g f sx
  _ | (Just y) with (g y)
    _ | Nothing = mapMaybeFusion g f sx
    _ | (Just z) = rewrite mapMaybeFusion g f sx in Refl

export
mapMaybeAppend : (f : a -> Maybe b) -> (sx, sy : SnocList a) -> mapMaybe f (sx ++ sy) = mapMaybe f sx ++ mapMaybe f sy
mapMaybeAppend f sx [<]       = Refl
mapMaybeAppend f sx (sy :< x) with (f x)
  _ | Nothing = mapMaybeAppend f sx sy
  _ | (Just y) = rewrite mapMaybeAppend f sx sy in Refl

export
toListMapMaybe : (f : a -> Maybe b) -> (sx : SnocList a) -> toList (mapMaybe f sx) = mapMaybe f (toList sx)
toListMapMaybe f [<]       = Refl
toListMapMaybe f (sx :< x) = do
  rewrite chipsAsListAppend sx [x]
  rewrite mapMaybeAppend f (toList sx) [x]
  rewrite mapMaybeStepLemma
  rewrite toListMapMaybe f sx
  Refl
  where
    mapMaybeStepLemma : toList (mapMaybe f (sx :< x)) = toList (mapMaybe f sx) ++ mapMaybe f [x]
    mapMaybeStepLemma with (f x)
      _ | Nothing  = rewrite appendNilRightNeutral $ toList $ mapMaybe f sx in Refl
      _ | (Just y) = rewrite chipsAsListAppend (mapMaybe f sx) [y] in Refl

export
mapMaybeCast : (f : a -> Maybe b) -> (xs : List a) -> mapMaybe f (cast {to=SnocList a} xs) = cast (mapMaybe f xs)
mapMaybeCast f []      = Refl
mapMaybeCast f (x::xs) = do
  rewrite fishAsSnocAppend [<x] xs
  rewrite mapMaybeAppend f [<x] (cast xs)
  rewrite mapMaybeStepLemma
  rewrite mapMaybeCast f xs
  Refl
  where
    mapMaybeStepLemma : cast (mapMaybe f (x::xs)) = mapMaybe f [<x] ++ cast (mapMaybe f xs)
    mapMaybeStepLemma with (f x)
      _ | Nothing  = rewrite appendLinLeftNeutral $ [<] <>< mapMaybe f xs in Refl
      _ | (Just y) = rewrite fishAsSnocAppend [<y] (mapMaybe f xs) in Refl
