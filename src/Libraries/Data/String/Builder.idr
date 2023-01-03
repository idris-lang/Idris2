||| This module contains a implementation of diff-lists
||| and an efficient string builder using them
module Libraries.Data.String.Builder

import Data.List

public export
record DiffList a where
    constructor MkDiffList
    append : List a -> List a

public export
(++) : DiffList a -> DiffList a -> DiffList a
xs ++ ys = MkDiffList $ \zs => xs.append (ys.append zs)

public export
toList : DiffList a -> List a
toList xs = xs.append []

public export
fromList : List a -> DiffList a
fromList xs = MkDiffList $ \ys => xs ++ ys

public export
Nil : DiffList a
Nil = MkDiffList id

public export
(::) : a -> DiffList a -> DiffList a
x :: xs = MkDiffList $ \ys => x :: xs.append ys

public export
singleton : a -> DiffList a
singleton x = MkDiffList $ \xs => x :: xs

export
intersperse : a -> List a -> DiffList a
intersperse sep [] = []
intersperse sep [x] = [x]
intersperse sep (x :: xs) = MkDiffList $ \ys => x :: go sep xs ys
  where
    go : a -> List a -> List a -> List a
    go sep [] ys = ys
    go sep (x :: xs) ys = sep :: x :: go sep xs ys

public export %inline
Semigroup (DiffList a) where
    xs <+> ys = xs ++ ys

public export %inline
Monoid (DiffList a) where
    neutral = []

public export
Builder : Type
Builder = DiffList String

public export %inline
FromString Builder where
    fromString = singleton

public export
char : Char -> Builder
char c = fromString $ cast c

export
sepBy : String -> List Builder -> Builder
sepBy sep [] = []
sepBy sep [x] = x
sepBy sep (x :: xs) = MkDiffList $ \ys => x.append $ go sep xs ys
  where
    go : String -> List Builder -> List String -> List String
    go sep [] ys = ys
    go sep (x :: xs) ys = sep :: x.append (go sep xs ys)

public export
build : Builder -> String
build = fastConcat . Builder.toList

public export
showB : Show a => a -> Builder
showB = singleton . show

export
toListFromListId : (xs : _) -> Builder.toList (Builder.fromList xs) === xs
toListFromListId [] = Refl
toListFromListId (x :: xs) = rewrite appendNilRightNeutral xs in Refl

export
toListNil : Builder.toList Nil = Nil
toListNil = Refl

export
appendCorrect : (xs, ys : _) -> Builder.toList (fromList xs ++ fromList ys) = xs ++ ys
appendCorrect xs ys = rewrite appendNilRightNeutral ys in Refl
