module Core.FC

import Data.Maybe
import Libraries.Text.Bounded
import Libraries.Text.PrettyPrint.Prettyprinter

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

||| A file context is a filename together with starting and ending positions.
||| It's often carried by AST nodes that might have been created from a source
||| file or by the compiler. That makes it useful to have the notion of
||| `EmptyFC` as part of the type.
public export
data FC = MkFC FileName FilePos FilePos
        | EmptyFC

||| A version of a file context that cannot be empty
public export
NonEmptyFC : Type
NonEmptyFC = (FileName, FilePos, FilePos)

------------------------------------------------------------------------
-- Conversion between NonEmptyFC and FC

||| NonEmptyFC always embeds into FC
export
justFC : NonEmptyFC -> FC
justFC (fname, start, end) = MkFC fname start end

||| A view checking whether an arbitrary FC happens to be non-empty
export
isNonEmptyFC : FC -> Maybe NonEmptyFC
isNonEmptyFC (MkFC fn start end) = Just (fn, start, end)
isNonEmptyFC EmptyFC = Nothing

export
defaultFC : NonEmptyFC
defaultFC = ("", (0, 0), (0, 0))

export
toNonEmptyFC : FC -> NonEmptyFC
toNonEmptyFC = fromMaybe defaultFC . isNonEmptyFC

------------------------------------------------------------------------
-- Projections

export
file : NonEmptyFC -> FileName
file (fn, _, _) = fn

export
startPos : NonEmptyFC -> FilePos
startPos (_, s, _) = s

export
startLine : NonEmptyFC -> Int
startLine = fst . startPos

export
startCol : NonEmptyFC -> Int
startCol = snd . startPos

export
endPos : NonEmptyFC -> FilePos
endPos (_, _, e) = e

export
endLine : NonEmptyFC -> Int
endLine = fst . endPos

export
endCol : NonEmptyFC -> Int
endCol = snd . endPos

------------------------------------------------------------------------
-- Smart constructors

export
boundToFC : FileName -> WithBounds t -> FC
boundToFC fname b = MkFC fname (start b) (end b)

------------------------------------------------------------------------
-- Predicates

--- Return whether a given file position is within the file context (assuming we're
--- in the right file)
export
within : FilePos -> NonEmptyFC -> Bool
within (x, y) (_, start, end)
   = (x, y) >= start && (x, y) <= end

-- Return whether a given line is on the same line as the file context (assuming
-- we're in the right file)
export
onLine : Int -> NonEmptyFC -> Bool
onLine x (_, start, end)
   = x >= fst start && x <= fst end

------------------------------------------------------------------------
-- Constant values

export
emptyFC : FC
emptyFC = EmptyFC

export
toplevelFC : FC
toplevelFC = MkFC "(toplevel)" (0, 0) (0, 0)

------------------------------------------------------------------------
-- Basic operations
export
mergeFC : FC -> FC -> Maybe FC
mergeFC (MkFC fname1 start1 end1) (MkFC fname2 start2 end2) =
  if fname1 == fname2
  then Just $ MkFC fname1 (min start1 start2) (max end1 end2)
  else Nothing
mergeFC _ _ = Nothing


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
  show EmptyFC = "EmptyFC"
  show (MkFC file startPos endPos) = file ++ ":" ++
             showPos startPos ++ "--" ++
             showPos endPos

export
Pretty FC where
  pretty EmptyFC = pretty "EmptyFC"
  pretty (MkFC file startPos endPos) = pretty file <+> colon
                 <+> prettyPos startPos <+> pretty "--"
                 <+> prettyPos endPos
    where
      prettyPos : FilePos -> Doc ann
      prettyPos (l, c) = pretty (l + 1) <+> colon <+> pretty (c + 1)
