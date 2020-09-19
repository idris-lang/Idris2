module Data.String.Iterator

%default total

export
data StringIterator : Type where [external]

%foreign
  "scheme:blodwen-string-iterator-new"
export
fromString : String -> StringIterator

%foreign
  "scheme:blodwen-string-iterator-next"
export
uncons : StringIterator -> Maybe (Char, StringIterator)

covering export
foldl : (a -> Char -> a) -> a -> String -> a
foldl f acc = loop acc . fromString
  where
    covering
    loop : a -> StringIterator -> a
    loop acc it =
      case uncons it of
        Nothing => acc
        Just (ch, it') => loop (f acc ch) it'
