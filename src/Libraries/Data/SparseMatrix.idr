module Libraries.Data.SparseMatrix

import Algebra.Semiring

import Libraries.Data.String.Builder
import Data.String

import Data.List1
import Data.Nat

import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util

%default total

lookupOrd : Ord k => k -> List (k, a) -> Maybe a
lookupOrd i [] = Nothing
lookupOrd i ((k, x) :: xs) =
  case compare i k of
    LT => Nothing
    EQ => Just x
    GT => lookupOrd i xs

export
lookupOrd1 : Ord k => k -> List1 (k, a) -> Maybe a
lookupOrd1 i ((k, x) ::: xs) =
  case compare i k of
    LT => Nothing
    EQ => Just x
    GT => lookupOrd i xs

namespace Vector
  public export
  Vector : Type -> Type
  Vector a = List (Nat, a)

  public export
  Vector1 : Type -> Type
  Vector1 a = List1 (Nat, a)

  fromList : (Eq a, Semiring a) => List a -> Vector a
  fromList = go Z
    where
      go : Nat -> List a -> Vector a
      go i [] = []
      go i (x :: xs)
          = if x == plusNeutral
               then go (S i) xs
               else (i, x) :: go (S i) xs

  fromList1 : (Eq a, Semiring a) => List a -> Maybe (Vector1 a)
  fromList1 = Data.List1.fromList . fromList

  insert : Nat -> a -> Vector a -> Vector a
  insert i x [] = [(i,x)]
  insert i x ys@((j, y) :: ys') =
    case compare i j of
      LT => (i, x) :: ys
      EQ => ys -- keep
      GT => (j, y) :: insert i x ys'

  export
  insert1 : Nat -> a -> Vector1 a -> Vector1 a
  insert1 i x ys@((j, y) ::: ys') =
    case compare i j of
      LT => (i, x) ::: (j, y) :: ys'
      EQ => ys -- keep
      GT => (j, y) ::: insert i x ys'

vectorFromList : List a -> Vector a
vectorFromList = go Z
  where
    go : Nat -> List a -> Vector a
    go i [] = []
    go i (x :: xs) = (i, x) :: go (S i) xs

rowFromList : (Eq a, Semiring a) => List a -> Maybe (Vector1 a)
rowFromList = fromList . go Z
  where
    go : Nat -> List a -> Vector a
    go i [] = []
    go i (x :: xs)
      = if x == plusNeutral
          then go (S i) xs
          else (i, x) :: go (S i) xs

public export
Matrix : Type -> Type
Matrix a = Vector (Vector1 a)

export
fromListList : (Eq a, Semiring a) => List (List a) -> Matrix a
fromListList = mapMaybe (\(i, xs) => map (i,) (rowFromList xs)) . vectorFromList

export
fromListVector : List (Vector a) -> Matrix a
fromListVector = mapMaybe (\(i, xs) => map (i,) (fromList xs)) . vectorFromList

transpose : Matrix a -> Matrix a
transpose [] = []
transpose ((i, xs) :: xss) = spreadHeads i (toList xs) (transpose xss) where
  spreadHeads : Nat -> Vector a -> Matrix a -> Matrix a
  spreadHeads i [] yss = yss
  spreadHeads i xs [] = map (\(j,x) => (j, singleton (i,x))) xs
  spreadHeads i xs@((j, x) :: xs') yss@((j', ys) :: yss') =
    case compare j j' of
      LT => (j, singleton (i,x)) :: spreadHeads i xs' yss
      EQ => (j', insert1 i x ys) :: spreadHeads i xs' yss'
      GT => (j', ys) :: spreadHeads i xs yss'

dot : Semiring a => Vector a -> Vector a -> a
dot [] _ = plusNeutral
dot _ [] = plusNeutral
dot xs@((k, x) :: xs') ys@((k', y) :: ys') =
  case compare k k' of
    LT => dot xs' ys
    EQ => (x |*| y) |+| dot xs' ys'
    GT => dot xs ys'

multRow : (Eq a, Semiring a) => Matrix a -> Vector1 a -> Vector a
multRow [] ys = []
multRow ((i, xs) :: xss) ys =
  let z = dot (toList xs) (toList ys) in
  if z == plusNeutral then
    multRow xss ys
  else
    (i, z) :: multRow xss ys

multTranspose : (Eq a, Semiring a) => Matrix a -> Matrix a -> Matrix a
multTranspose xss [] = []
multTranspose xss ((j, ys) :: yss) =
  case multRow xss ys of
    [] => multTranspose xss yss
    y' :: ys' => (j, y' ::: ys') :: multTranspose xss yss

export
mult : (Eq a, Semiring a) => Matrix a -> Matrix a -> Matrix a
mult = multTranspose . transpose

maxIndex1 : Vector1 a -> Nat
maxIndex1 ((i, x) ::: xs) = maybe i fst (last' xs)

maxIndexInner : Matrix a -> Nat
maxIndexInner = foldMap @{%search} @{MkMonoid @{MkSemigroup max} 0} (maxIndex1 . snd)

namespace Pretty
  header : (columnWidth : Int) -> (rowLength : Nat) -> List (Doc ann)
  header columnWidth rowLength = map (fill columnWidth . byShow) (take rowLength [0..])

  export
  maxIndex : Vector a -> Nat
  maxIndex xs = maybe 0 fst (last' xs)

  export
  row : Pretty ann a => Vector a -> List (Doc ann)
  row xs = go rowLength xs
    where
      rowLength : Nat
      rowLength = maxIndex xs + 1

      prettyNeutral : Doc ann
      prettyNeutral = space

      go : Nat -> Vector a -> List (Doc ann)
      go _ [] = []
      go Z _ = []
      go i@(S i') ys@((j, y) :: ys') =
        case compare (minus rowLength i) j of
          LT => prettyNeutral :: go i' ys
          EQ => pretty y :: go i' ys'
          GT => go i ys'


  export
  row1 : Pretty ann a => Vector1 a -> List (Doc ann)
  row1 ys = row (toList ys)

  columnSeparator : Doc ann
  columnSeparator = spaces 3

  columnSep : List (Doc ann) -> Doc ann
  columnSep = concatWith (\x, y => x <+> columnSeparator <+> y)

  export
  prettyRow1 : Pretty ann a => (index : Doc ann) -> (columnWidth : Int) -> Vector1 a -> Doc ann
  prettyRow1 index columnWidth ys = columnSep $ map (fill columnWidth) (index :: row1 ys)

  hardlineSep : List (Doc ann) -> Doc ann
  hardlineSep = concatWith (\x, y => x <+> hardline <+> y)

  export
  prettyTable : Pretty ann a => (maxWidthA : Nat) -> Matrix a -> Doc ann
  prettyTable maxWidthA m = hardlineSep $
      -- header
      columnSep (spaces widthJ :: header widthI (maxI + 1))
      -- content
        :: map (\(j, r) => prettyRow1 (fill widthJ (byShow j)) widthI r) m
    where
      maxI : Nat
      maxI = maxIndexInner m

      maxJ : Nat
      maxJ = maxIndex m

      widthI : Int
      widthI = cast $ max (length (show maxI)) maxWidthA

      widthJ : Int
      widthJ = cast $ length (show maxJ)
