module Protocol.SExp

import Data.List
import Data.List1

%default total

-- should be in base somewhere!
join : String -> List String -> String
join sep xs = concat $ intersperse sep xs

public export
data SExp = SExpList (List SExp)
          | StringAtom String
          | BoolAtom Bool
          | IntegerAtom Integer
          | SymbolAtom String

escape : String -> String
escape = pack . concatMap escapeChar . unpack
  where
    escapeChar : Char -> List Char
    escapeChar '\\' = ['\\', '\\']
    escapeChar '"'  = ['\\', '\"']
    escapeChar c    = [c]

export
Show SExp where
  show (SExpList xs) = assert_total $ "(" ++ join " " (map show xs) ++ ")"
  show (StringAtom str) = "\"" ++ escape str ++ "\""
  show (BoolAtom b) = ":" ++ show b
  show (IntegerAtom i) = show i
  show (SymbolAtom s) = ":" ++ s

public export
interface SExpable a where
  toSExp : a -> SExp

-- TODO: Merge these into 1 interface later
public export
interface FromSExpable a where
  fromSExp : SExp -> Maybe a

export
SExpable SExp where
  toSExp = id

export
SExpable Bool where
  toSExp = BoolAtom

export
FromSExpable Bool where
  fromSExp (BoolAtom b) = Just b
  fromSExp _ = Nothing

export
SExpable String where
  toSExp = StringAtom

export
FromSExpable String where
  fromSExp (StringAtom s) = Just s
  fromSExp _ = Nothing

export
SExpable Integer where
  toSExp = IntegerAtom

export
FromSExpable Integer where
  fromSExp (IntegerAtom a) = Just a
  fromSExp _ = Nothing

export
SExpable Int where
  toSExp = IntegerAtom . cast

export
FromSExpable Int where
  fromSExp a = do Just $ cast {from = Integer }$ !(fromSExp a)

export
SExpable Nat where
  toSExp = IntegerAtom . cast

export
FromSExpable Nat where
  fromSExp a = do Just $ cast {from = Integer }$ !(fromSExp a)

export
(SExpable a, SExpable b) => SExpable (a, b) where
  toSExp (x, y)
      = case toSExp y of
             SExpList xs => SExpList (toSExp x :: xs)
             y' => SExpList [toSExp x, y']

export
(FromSExpable a, FromSExpable b) => FromSExpable (a, b) where
  fromSExp (SExpList xs) = case xs of
    [x,y] => do pure $ (!(fromSExp x), !(fromSExp y))
    (x :: xs) => do pure $ (!(fromSExp x), !(fromSExp $ SExpList xs))
    _ => Nothing
  fromSExp _ = Nothing

export
SExpable a => SExpable (List a) where
  toSExp xs
      = SExpList (map toSExp xs)

export
FromSExpable a => FromSExpable (List a) where
  fromSExp (SExpList sexps) = traverse fromSExp sexps
  fromSExp _ = Nothing

export
SExpable a => SExpable (List1 a) where
  toSExp xs
      = SExpList (map toSExp (toList xs))

export
FromSExpable a => FromSExpable (List1 a) where
  fromSExp (SExpList (sexp :: sexps)) = traverse fromSExp (sexp ::: sexps)
  fromSExp _ = Nothing

export
SExpable a => SExpable (Maybe a) where
  toSExp Nothing = SExpList []
  toSExp (Just x) = toSExp x
