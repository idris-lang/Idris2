module Data.Stream.Extra

%default total

||| Insert elements from a Foldable at the start of an existing Stream
||| @ pfx the Foldable containing elements to prepend
||| @ stream the Stream to prepend the elements to
public export
startWith : Foldable t => (pfx : t a) -> (stream : Stream a) -> Stream a
startWith pfx stream = foldr (\x, xs => x :: xs) stream pfx
