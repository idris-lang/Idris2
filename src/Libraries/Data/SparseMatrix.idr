module Libraries.Data.SparseMatrix

import Algebra.Semiring

import Data.List1
import Data.Maybe
import Data.String

import Libraries.Text.PrettyPrint.Prettyprinter

%default total

namespace Vector
  ||| A sparse vector is a list of pairs consisting of an index and its
  ||| corresponding element.
  |||
  ||| Invariants:
  ||| - indices must appear in order and should to be duplicate-free,
  ||| - elements must be additively non-neutral,
  ||| - missing entries are assumed to be neutral.
  public export
  Vector : Type -> Type
  Vector a = List (Nat, a)

  ||| Turns a list into a sparse vector, discarding neutral elements in
  ||| the process.
  export
  fromList : (Eq a, Semiring a) => List a -> Vector a
  fromList = go Z
    where
      go : Nat -> List a -> Vector a
      go i [] = []
      go i (x :: xs)
          = if x == plusNeutral
               then go (S i) xs
               else (i, x) :: go (S i) xs

  ||| Insert `x` at index `i`. Ignore if the `i`th element already
  ||| exists.
  |||
  ||| @ x must not be neutral
  export
  insert : (i : Nat) -> (x : a) -> Vector a -> Vector a
  insert i x [] = [(i,x)]
  insert i x ys@((j, y) :: ys') =
    case compare i j of
      LT => (i, x) :: ys
      EQ => ys -- keep
      GT => (j, y) :: insert i x ys'

  export
  lookupOrd : Ord k => k -> List (k, a) -> Maybe a
  lookupOrd i [] = Nothing
  lookupOrd i ((k, x) :: xs) =
    case compare i k of
      LT => Nothing
      EQ => Just x
      GT => lookupOrd i xs

  export
  maxIndex : Vector a -> Maybe Nat
  maxIndex xs = map fst (last' xs)

  export
  length : Vector a -> Nat
  length = maybe 0 ((+) 1) . maxIndex

  export
  dot : Semiring a => Vector a -> Vector a -> a
  dot [] _ = plusNeutral
  dot _ [] = plusNeutral
  dot xs@((k, x) :: xs') ys@((k', y) :: ys') =
    case compare k k' of
      LT => dot xs' ys
      EQ => (x |*| y) |+| dot xs' ys'
      GT => dot xs ys'

namespace Vector1
  public export
  Vector1 : Type -> Type
  Vector1 a = List1 (Nat, a)

  export
  fromList : (Eq a, Semiring a) => List a -> Maybe (Vector1 a)
  fromList = Data.List1.fromList . Vector.fromList

  export
  insert : Nat -> a -> Vector1 a -> Vector1 a
  insert i x ys@((j, y) ::: ys') =
    case compare i j of
      LT => (i, x) ::: (j, y) :: ys'
      EQ => ys -- keep
      GT => (j, y) ::: insert i x ys'

  export
  lookupOrd : Ord k => k -> List1 (k, a) -> Maybe a
  lookupOrd i ((k, x) ::: xs) =
    case compare i k of
      LT => Nothing
      EQ => Just x
      GT => lookupOrd i xs

  export
  maxIndex : Vector1 a -> Nat
  maxIndex ((i, x) ::: xs) = maybe i fst (last' xs)

||| A sparse matrix is a sparse vector of (non-empty) sparse vectors.
public export
Matrix : Type -> Type
Matrix a = Vector (Vector1 a)

export
fromSparseList : List (Maybe (Nat, a)) -> Matrix a
fromSparseList xs =
    let inner_vector = withIndex $ map (Data.List1.fromList . toList) xs
    in mapMaybe (\(i, m) => map (i,) m) inner_vector
  where
    withIndex : List b -> List (Nat, b)
    withIndex = go 0
      where
        go : Nat -> List b -> List (Nat, b)
        go _ [] = []
        go i (x :: xs) = (i, x) :: go (S i) xs

export
fromListList : (Eq a, Semiring a) => List (List a) -> Matrix a
fromListList = mapMaybe (\(i, xs) => map (i,) (Vector1.fromList xs)) . withIndex
  where
    -- may contain empty lists
    withIndex : List (List a) -> List (Nat, List a)
    withIndex = go Z
      where
        go : Nat -> List (List a) -> List (Nat, List a)
        go i [] = []
        go i (x :: xs) = (i, x) :: go (S i) xs

export
transpose : Matrix a -> Matrix a
transpose [] = []
transpose ((i, xs) :: xss) = spreadHeads i (toList xs) (transpose xss) where
  spreadHeads : Nat -> Vector a -> Matrix a -> Matrix a
  spreadHeads i [] yss = yss
  spreadHeads i xs [] = map (\(j,x) => (j, singleton (i,x))) xs
  spreadHeads i xs@((j, x) :: xs') yss@((j', ys) :: yss') =
    case compare j j' of
      LT => (j, singleton (i,x)) :: spreadHeads i xs' yss
      EQ => (j', insert i x ys) :: spreadHeads i xs' yss'
      GT => (j', ys) :: spreadHeads i xs yss'

multRow : (Eq a, Semiring a) => Matrix a -> Vector1 a -> Vector a
multRow [] ys = []
multRow ((i, xs) :: xss) ys =
  let z = dot (toList xs) (toList ys) in
  if z == plusNeutral then
    multRow xss ys
  else
    (i, z) :: multRow xss ys

||| Given matrices `xss` and `yss`, computes `xss^T * yss`.
multTranspose : (Eq a, Semiring a) => (xss : Matrix a) -> (yss : Matrix a) -> Matrix a
multTranspose xss [] = []
multTranspose xss ((j, ys) :: yss) =
  case multRow xss ys of
    [] => multTranspose xss yss -- discard empty rows
    y' :: ys' => (j, y' ::: ys') :: multTranspose xss yss

export
mult : (Eq a, Semiring a) => Matrix a -> Matrix a -> Matrix a
mult = multTranspose . transpose

||| Find largest column index.
maxColumnIndex : Matrix a -> Maybe Nat
maxColumnIndex = foldMap @{%search} @{Monoid.Deep @{MkSemigroup max}} (Just . maxIndex . snd)

namespace Pretty
  header : (columnWidth : Int) -> (length : Nat) -> List (Doc ann)
  header columnWidth length = map (fill columnWidth . byShow) (take length [0..])

  row : Pretty ann a => Vector a -> List (Doc ann)
  row xs = go rowLength xs
    where
      rowLength : Nat
      rowLength = Vector.length xs

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

  -- space between columns
  columnSpacing : Int
  columnSpacing = 1

  columnSep : List (Doc ann) -> Doc ann
  columnSep = concatWith (\x, y => x <+> spaces columnSpacing <+> y)

  row1 : Pretty ann a => (columnWidth : Int) -> Vector1 a -> List (Doc ann)
  row1 columnWidth ys = map (fill columnWidth) (row (toList ys))

  hardlineSep : List (Doc ann) -> Doc ann
  hardlineSep = concatWith (\x, y => x <+> hardline <+> y)

  ||| Renders a matrix as an ASCII table of the following shape:
  |||
  ||| ```
  |||                columnSpacing
  |||                      __
  |||         columnDesc  0  1  ...
  ||| rowDesc +--------------------
  ||| 0       |           a  b
  ||| 1       |           c  d
  ||| ...     |           ...
  |||```
  |||
  ||| Note: everything is sadly left-aligned.
  |||
  ||| @ maxWidthA Maximal length rendering something of type `a` might reach.
  export
  prettyTable : Pretty ann a => (rowDesc, columnDesc : String) -> (maxWidthA : Nat) -> Matrix a -> Doc ann
  prettyTable rowDesc columnDesc maxWidthA m = hardlineSep $
      -- header
      (spaces rowLabelWidth <++> columnSep (pretty0 columnDesc :: header columnWidth columnCount))
      -- separator
        :: (fill rowLabelWidth (pretty0 rowDesc) <++> Chara intersectionLabelSep <+> replicateChar columnLabelSepLength columnLabelSep)
      -- content
        :: map (\(j, r) => fill rowLabelWidth (byShow j) <++> columnSep (fill (cast (length columnDesc)) (Chara rowLabelSep) :: row1 columnWidth r)) m
    where
      rowLabelSep, columnLabelSep, intersectionLabelSep : Char
      rowLabelSep = '|'
      columnLabelSep = '-'
      intersectionLabelSep = '+'

      rowMax, columnMax : Maybe Nat
      rowMax = maxIndex m
      columnMax = maxColumnIndex m

      rowMaxIndexWidth, columnMaxIndexWidth : Nat
      rowMaxIndexWidth = maybe 0 (length . show) rowMax
      columnMaxIndexWidth = maybe 0 (length . show) columnMax

      rowLabelWidth : Int
      rowLabelWidth = cast $ max rowMaxIndexWidth (length rowDesc)

      columnWidth : Int
      columnWidth = cast $ max columnMaxIndexWidth maxWidthA

      columnCount : Nat
      columnCount = maybe 0 ((+) 1) columnMax

      columnLabelSepLength : Int
      columnLabelSepLength =
        cast (minus (length columnDesc) 1) -- columnDesc overlaps with *LabelSep
        + (columnWidth + columnSpacing) * cast columnCount
