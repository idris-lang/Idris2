module Data.String.Iterator

export
record StringIterator where
  constructor MkSI
  string : String

  -- backend-dependent offset into the string
  -- see prim__readChar below
  offset : Int

export
fromString : String -> StringIterator
fromString s = MkSI s 0

private
data ReadResult
  = EOF
  | Character Char Int  -- character + width in backend-dependent units

-- Runs in O(1) time.
-- Takes a backend-dependent offset into the string.
-- On ML-based backends, this is in bytes;
-- in Scheme, this is in codepoints.
private
%foreign "scheme:read-string-char"
prim__readChar : Int -> String -> ReadResult

export
uncons : StringIterator -> Maybe (Char, StringIterator)
uncons (MkSI s ofs) =
  case prim__readChar ofs s of
    EOF => Nothing
    Character ch width => Just (ch, MkSI s (ofs + width))

export
foldl : (a -> Char -> a) -> a -> String -> a
foldl f acc s = loop 0 acc
  where
    loop : Int -> a -> a
    loop ofs acc =
      case prim__readChar ofs s of
        EOF => acc
        Character ch width => loop (ofs + width) (f acc ch)
