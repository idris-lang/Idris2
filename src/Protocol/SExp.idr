module Protocol.SExp

import Data.List

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
