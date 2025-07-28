module Core.FC

import Core.Name.Namespace

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

public export
data VirtualIdent : Type where
  Interactive : VirtualIdent

public export
Eq VirtualIdent where
  Interactive == Interactive = True

export
Show VirtualIdent where
  show Interactive = "(Interactive)"

public export
data OriginDesc : Type where
  ||| Anything that originates in physical Idris source files is assigned a
  ||| `PhysicalIdrSrc modIdent`,
  |||   where `modIdent` is the top-level module identifier of that file.
  PhysicalIdrSrc : (ident : ModuleIdent) -> OriginDesc
  ||| Anything parsed from a package file is decorated with `PhysicalPkgSrc fname`,
  |||   where `fname` is path to the package file.
  PhysicalPkgSrc : (fname : FileName) -> OriginDesc
  Virtual : (ident : VirtualIdent) -> OriginDesc

public export
Eq OriginDesc where
  PhysicalIdrSrc ident == PhysicalIdrSrc ident' = ident == ident'
  PhysicalPkgSrc fname == PhysicalPkgSrc fname' = fname == fname'
  Virtual ident        == Virtual ident'        = ident == ident'
  _                    == _                     = False

export
Show OriginDesc where
  show (PhysicalIdrSrc ident) = show ident
  show (PhysicalPkgSrc fname) = show fname
  show (Virtual ident) = show ident

||| A file context is a filename together with starting and ending positions.
||| It's often carried by AST nodes that might have been created from a source
||| file or by the compiler. That makes it useful to have the notion of
||| `EmptyFC` as part of the type.
public export
data FC = MkFC        OriginDesc FilePos FilePos
        | ||| Virtual FCs are FC attached to desugared/generated code. They can help with marking
          ||| errors, but we shouldn't attach semantic highlighting metadata to them.
          MkVirtualFC OriginDesc FilePos FilePos
        | EmptyFC

%name FC fc

||| A version of a file context that cannot be empty
public export
NonEmptyFC : Type
NonEmptyFC = (OriginDesc, FilePos, FilePos)

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
isNonEmptyFC (MkVirtualFC fn start end) = Just (fn, start, end)
isNonEmptyFC EmptyFC = Nothing

||| A view checking whether an arbitrary FC originates from a source location
export
isConcreteFC : FC -> Maybe NonEmptyFC
isConcreteFC (MkFC fn start end) = Just (fn, start, end)
isConcreteFC _ = Nothing

||| Turn an FC into a virtual one
export
virtualiseFC : FC -> FC
virtualiseFC (MkFC fn start end) = MkVirtualFC fn start end
virtualiseFC fc = fc

export
defaultFC : NonEmptyFC
defaultFC = (Virtual Interactive, (0, 0), (0, 0))

export
replFC : FC
replFC = justFC defaultFC

export
toNonEmptyFC : FC -> NonEmptyFC
toNonEmptyFC = fromMaybe defaultFC . isNonEmptyFC

------------------------------------------------------------------------
-- Projections

export
origin : NonEmptyFC -> OriginDesc
origin (fn, _, _) = fn

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
boundToFC : OriginDesc -> WithBounds t -> FC
boundToFC mbModIdent b = MkFC mbModIdent (start b) (end b)

export
(.toFC) : (o : OriginDesc) => WithBounds t -> FC
x.toFC = boundToFC o x

export
boundToFC' : OriginDesc -> Bounds -> FC
boundToFC' mbModIdent b = MkFC mbModIdent (startBounds b) (endBounds b)

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
  (==) (MkVirtualFC n s e) (MkVirtualFC n' s' e') = n == n' && s == s' && e == e'
  (==) EmptyFC EmptyFC = True
  (==) _ _ = False

export
Show FC where
  show EmptyFC = "EmptyFC"
  show (MkFC ident startPos endPos) = show ident ++ ":" ++
             showPos startPos ++ "--" ++
             showPos endPos
  show (MkVirtualFC ident startPos endPos) = show ident ++ ":" ++
             showPos startPos ++ "--" ++
             showPos endPos

prettyPos : FilePos -> Doc Void
prettyPos = pretty . showPos

export
Pretty Void FC where
  pretty EmptyFC = pretty "EmptyFC"
  pretty (MkFC ident startPos endPos) = byShow ident <+> colon
                 <+> prettyPos startPos <+> pretty "--"
                 <+> prettyPos endPos
  pretty (MkVirtualFC ident startPos endPos) = byShow ident <+> colon
                 <+> prettyPos startPos <+> pretty "--"
                 <+> prettyPos endPos
