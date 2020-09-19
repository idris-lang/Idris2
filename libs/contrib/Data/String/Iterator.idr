module Data.String.Iterator

import public Data.List.Lazy

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

export
unpack : String -> LazyList Char
unpack = unsafeUnfoldr uncons . fromString
