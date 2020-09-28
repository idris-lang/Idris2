module Core.FC

import Text.Bounded
import Text.PrettyPrint.Prettyprinter

%default total

------------------------------------------------------------------------
-- Types

public export
FilePos : Type
FilePos = (Int, Int)

showPos : FilePos -> String
showPos (l, c) = show (l + 1) ++ ":" ++ show (c + 1)

public export
FileName : Type
FileName = String

||| A file context is a filename together with starting and ending positions
public export
data FC = MkFC FileName FilePos FilePos
        | EmptyFC

------------------------------------------------------------------------
-- Projections

export
file : FC -> FileName
file (MkFC fn _ _) = fn
file EmptyFC = ""

export
startPos : FC -> FilePos
startPos (MkFC _ s _) = s
startPos EmptyFC = (0, 0)

export
endPos : FC -> FilePos
endPos (MkFC _ _ e) = e
endPos EmptyFC = (0, 0)

------------------------------------------------------------------------
-- Smart constructor

export
boundToFC : FileName -> WithBounds t -> FC
boundToFC fname b = MkFC fname (start b) (end b)

------------------------------------------------------------------------
-- Predicates

-- Return whether a given file position is within the file context (assuming we're
-- in the right file)
export
within : FilePos -> FC -> Bool
within (x, y) (MkFC _ start end)
   = (x, y) >= start && (x, y) <= end
within _ _ = False

-- Return whether a given line is on the same line as the file context (assuming
-- we're in the right file)
export
onLine : Int -> FC -> Bool
onLine x (MkFC _ start end)
   = x >= fst start && x <= fst end
onLine _ _ = False

------------------------------------------------------------------------
-- Constant values

export
emptyFC : FC
emptyFC = EmptyFC

export
toplevelFC : FC
toplevelFC = MkFC "(toplevel)" (0, 0) (0, 0)

%name FC fc

------------------------------------------------------------------------
-- Instances

export
Eq FC where
  (==) (MkFC n s e) (MkFC n' s' e') = n == n' && s == s' && e == e'
  (==) EmptyFC EmptyFC = True
  (==) _ _ = False

export
Show FC where
  show loc = file loc ++ ":" ++
             showPos (startPos loc) ++ "--" ++
             showPos (endPos loc)

export
Pretty FC where
  pretty loc = pretty (file loc) <+> colon
                 <+> prettyPos (startPos loc) <+> pretty "--"
                 <+> prettyPos (endPos loc)
    where
      prettyPos : FilePos -> Doc ann
      prettyPos (l, c) = pretty (l + 1) <+> colon <+> pretty (c + 1)
