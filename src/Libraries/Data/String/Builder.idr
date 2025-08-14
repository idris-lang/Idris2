||| This module contains an efficient string builder
module Libraries.Data.String.Builder

import public Libraries.Data.DList

export
intersperse : a -> List a -> DList a
intersperse sep [] = []
intersperse sep [x] = [x]
intersperse sep (x :: xs) = x :: go sep xs
  where
    go : a -> List a -> DList a
    go sep [] = []
    go sep (x :: xs) = sep :: x :: go sep xs

public export
Builder : Type
Builder = DList String

public export
char : Char -> Builder
char c = fromString $ cast c

export
sepBy : String -> List Builder -> Builder
sepBy sep [] = []
sepBy sep [x] = x
sepBy sep (x :: xs) = x ++ go sep xs
  where
    go : String -> List Builder -> Builder
    go sep [] = []
    go sep (x :: xs) = sep :: x ++ go sep xs

public export
build : Builder -> String
build = fastConcat . reify

public export
showB : Show a => a -> Builder
showB = singleton . show
