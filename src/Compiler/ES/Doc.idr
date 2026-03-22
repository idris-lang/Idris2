module Compiler.ES.Doc

import Data.List
import Core.FC

public export
data Doc
  = Nil
  | LineBreak
  | SoftSpace -- this will be ignored in compact printing
  | Comment Doc -- this will be ignored in compact printing
  | Text String
  | Nest Nat Doc
  | Seq Doc Doc
  | Loc FC Doc -- source location annotation for source maps

export
Semigroup Doc where
  Nil <+> y = y
  x <+> Nil = x
  x <+> y = Seq x y

export
Monoid Doc where
  neutral = Nil

public export %inline
shown : Show a => a -> Doc
shown a = Text (show a)

export %inline
comment : Doc -> Doc
comment = Comment

export
FromString Doc where
  fromString = Text

export
isMultiline : Doc -> Bool
isMultiline []         = False
isMultiline LineBreak  = True
isMultiline SoftSpace  = False
isMultiline (Text x)   = False
isMultiline (Comment x) = isMultiline x
isMultiline (Nest k x) = isMultiline x
isMultiline (Seq x y)  = isMultiline x || isMultiline y
isMultiline (Loc _ x)  = isMultiline x

export
(<++>) : Doc -> Doc -> Doc
(<++>) a b = a <+> " " <+> b

export
vcat : List Doc -> Doc
vcat = concat . intersperse LineBreak

export
hcat : List Doc -> Doc
hcat = concat

export
hsep : List Doc -> Doc
hsep = concat . intersperse " "

export
block : Doc -> Doc
block b = concat ["{", Nest 1 (LineBreak <+> b), LineBreak, "}"]

export
paren : Doc -> Doc
paren d = "(" <+> d <+> ")"

export
lambdaArrow : Doc
lambdaArrow = SoftSpace <+> "=>" <+> SoftSpace

export
softComma : Doc
softComma = "," <+> SoftSpace

export
softColon : Doc
softColon = ":" <+> SoftSpace

export
softEq : Doc
softEq = SoftSpace <+> "=" <+> SoftSpace

export
compact : Doc -> String
compact = fastConcat . go
  where go : Doc -> List String
        go Nil        = []
        go LineBreak  = []
        go SoftSpace  = []
        go (Comment _) = []
        go (Text x)   = [x]
        go (Nest _ y) = go y
        go (Seq x y)  = go x ++ go y
        go (Loc _ y)  = go y

export
pretty : Doc -> String
pretty = fastConcat . go ""
  where nSpaces : Nat -> String
        nSpaces n = fastPack $ replicate n ' '

        go : (spaces : String) -> Doc -> List String
        go _ Nil        = []
        go s LineBreak  = ["\n",s]
        go _ SoftSpace  = [" "]
        go s (Comment x) = "/* " :: go s x ++ [" */"]
        go _ (Text x)   = [x]
        go s (Nest x y) = go (s ++ nSpaces x) y
        go s (Seq x y)  = go s x ++ go s y
        go s (Loc _ y)  = go s y

--------------------------------------------------------------------------------
--          Source Map Support
--------------------------------------------------------------------------------

||| A source mapping entry
||| (sourceFile, sourceLine, sourceCol, generatedLine, generatedCol)
public export
record SourceMapping where
  constructor MkSourceMapping
  srcOrigin : OriginDesc
  srcLine   : Int
  srcCol    : Int
  genLine   : Int
  genCol    : Int

export
Show SourceMapping where
  show m = "SourceMapping(\{show m.srcOrigin}:\{show m.srcLine}:\{show m.srcCol} -> gen:\{show m.genLine}:\{show m.genCol})"

||| Render state for tracking generated positions
record RenderState where
  constructor MkRenderState
  line     : Int      -- current generated line (0-indexed)
  col      : Int      -- current generated column (0-indexed)
  mappings : List SourceMapping

initRenderState : RenderState
initRenderState = MkRenderState 0 0 []

||| Pretty print with source mappings
||| Returns the generated code and list of source mappings
export
prettyWithMappings : Doc -> (String, List SourceMapping)
prettyWithMappings doc =
  let (strs, finalState) = go "" initRenderState doc
  in (fastConcat strs, reverse finalState.mappings)
  where
    nSpaces : Nat -> String
    nSpaces n = fastPack $ replicate n ' '

    -- Calculate new position after emitting a string
    updatePos : RenderState -> String -> RenderState
    updatePos st s =
      let chars = unpack s
          newlines = length $ filter (== '\n') chars
      in if newlines > 0
         then let lastLineLen = length $ takeWhile (/= '\n') $ reverse chars
              in { line := st.line + cast newlines, col := cast lastLineLen } st
         else { col := st.col + cast (length chars) } st

    -- Add a mapping if FC is non-empty
    addMapping : RenderState -> FC -> RenderState
    addMapping st fc = case isNonEmptyFC fc of
      Nothing => st
      Just (origin, (srcL, srcC), _) =>
        { mappings := MkSourceMapping origin srcL srcC st.line st.col :: st.mappings } st

    go : (spaces : String) -> RenderState -> Doc -> (List String, RenderState)
    go _ st Nil        = ([], st)
    go s st LineBreak  =
      let st' = { line := st.line + 1, col := cast (length s) } st
      in (["\n" ++ s], st')
    go _ st SoftSpace  = ([" "], { col := st.col + 1 } st)
    go s st (Comment x) =
      let result = go s st x
          xs = fst result
          st1 = snd result
          st2 = updatePos st1 (fastConcat xs)
      in ("/* " :: xs ++ [" */"], updatePos st2 "/*  */")
    go _ st (Text x)   = ([x], updatePos st x)
    go s st (Nest x y) = go (s ++ nSpaces x) st y
    go s st (Seq x y)  =
      let result1 = go s st x
          xs = fst result1
          st1 = snd result1
          result2 = go s st1 y
          ys = fst result2
          st2 = snd result2
      in (xs ++ ys, st2)
    go s st (Loc fc y) = go s (addMapping st fc) y
