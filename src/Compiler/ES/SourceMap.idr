||| Source Map v3 generation for JavaScript output
||| See: https://sourcemaps.info/spec.html
module Compiler.ES.SourceMap

import Data.List
import Data.String
import Data.SortedMap
import Core.FC
import Core.Name.Namespace  -- For Show ModuleIdent instance
import Compiler.ES.Doc

%default covering  -- VLQ encoding uses recursive functions

--------------------------------------------------------------------------------
--          VLQ Encoding
--------------------------------------------------------------------------------

||| Base64 VLQ alphabet
vlqAlphabet : String
vlqAlphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

||| Get character at index in VLQ alphabet
vlqChar : Int -> Char
vlqChar n =
  let idx = cast {to=Nat} n
      chars = unpack vlqAlphabet
  in case getAt idx chars of
       Just c  => c
       Nothing => 'A'  -- fallback, shouldn't happen

||| VLQ continuation bit (6th bit)
vlqContinuationBit : Int
vlqContinuationBit = 32  -- 0b100000

||| VLQ sign bit (1st bit)
vlqSignBit : Int
vlqSignBit = 1

||| Encode a signed integer to VLQ
||| Returns list of base64 characters
export
encodeVLQ : Int -> List Char
encodeVLQ n =
  let -- Convert to VLQ signed representation
      -- Negative: (abs(n) << 1) | 1
      -- Positive: n << 1
      vlqSigned = if n < 0
                  then ((-n) * 2) + 1
                  else n * 2
  in encodeUnsigned vlqSigned []
  where
    encodeUnsigned : Int -> List Char -> List Char
    encodeUnsigned val acc =
      let digit = val `mod` 32      -- 5 bits of data
          rest  = val `div` 32
          -- Set continuation bit if more data follows
          encoded = if rest > 0
                    then digit + vlqContinuationBit
                    else digit
      in if rest > 0
         then encodeUnsigned rest (vlqChar encoded :: acc)
         else reverse (vlqChar encoded :: acc)

||| Encode a list of integers to VLQ string
export
encodeVLQList : List Int -> String
encodeVLQList = fastPack . concatMap encodeVLQ

--------------------------------------------------------------------------------
--          Source Index Management
--------------------------------------------------------------------------------

||| Build source file index from mappings
||| Returns (indexed sources list, mapping from OriginDesc to index)
export
buildSourceIndex : List SourceMapping -> (List OriginDesc, SortedMap String Int)
buildSourceIndex mappings =
  let origins = nub $ map srcOrigin mappings
      indexed = zip [0..length origins] origins
      indexMap = fromList $ map (\(i, o) => (show o, cast i)) indexed
  in (origins, indexMap)

--------------------------------------------------------------------------------
--          Mappings Encoding
--------------------------------------------------------------------------------

||| State for incremental VLQ encoding
record MappingState where
  constructor MkMappingState
  prevGenCol   : Int  -- previous generated column
  prevSrcIdx   : Int  -- previous source index
  prevSrcLine  : Int  -- previous source line
  prevSrcCol   : Int  -- previous source column
  prevGenLine  : Int  -- previous generated line (for semicolons)

initMappingState : MappingState
initMappingState = MkMappingState 0 0 0 0 0

||| Encode a single mapping segment
||| Each segment: [genCol, srcIdx, srcLine, srcCol] as VLQ deltas
encodeSegment : SortedMap String Int -> MappingState -> SourceMapping -> (String, MappingState)
encodeSegment srcIndex st m =
  case lookup (show m.srcOrigin) srcIndex of
    Nothing => ("", st)  -- unknown source, skip
    Just srcIdx =>
      let -- All values are deltas from previous
          genColDelta   = m.genCol - st.prevGenCol
          srcIdxDelta   = srcIdx - st.prevSrcIdx
          srcLineDelta  = m.srcLine - st.prevSrcLine
          srcColDelta   = m.srcCol - st.prevSrcCol

          segment = encodeVLQList [genColDelta, srcIdxDelta, srcLineDelta, srcColDelta]

          newState = MkMappingState m.genCol srcIdx m.srcLine m.srcCol m.genLine
      in (segment, newState)

||| Group mappings by generated line
groupByLine : List SourceMapping -> List (Int, List SourceMapping)
groupByLine mappings =
  let sorted = sortBy (\a, b => compare (a.genLine, a.genCol) (b.genLine, b.genCol)) mappings
  in groupByLineHelper sorted []
  where
    groupByLineHelper : List SourceMapping -> List (Int, List SourceMapping) -> List (Int, List SourceMapping)
    groupByLineHelper [] acc = reverse $ map (\(l, ms) => (l, reverse ms)) acc
    groupByLineHelper (m :: ms) [] = groupByLineHelper ms [(m.genLine, [m])]
    groupByLineHelper (m :: ms) ((curLine, curMappings) :: rest) =
      if m.genLine == curLine
      then groupByLineHelper ms ((curLine, m :: curMappings) :: rest)
      else groupByLineHelper ms ((m.genLine, [m]) :: (curLine, curMappings) :: rest)

||| Encode all mappings to source map mappings string
||| Lines are separated by ';', segments within a line by ','
export
encodeMappings : SortedMap String Int -> List SourceMapping -> String
encodeMappings srcIndex mappings =
  let grouped = groupByLine mappings
      maxLine = foldl (\acc, (l, _) => max acc l) 0 grouped
  in encodeLines 0 maxLine initMappingState grouped
  where
    encodeLineSegments : MappingState -> List SourceMapping -> (String, MappingState)
    encodeLineSegments st [] = ("", st)
    encodeLineSegments st (m :: ms) =
      let result1 = encodeSegment srcIndex st m
          seg = fst result1
          st' = snd result1
          -- For subsequent segments, don't reset genCol (it's cumulative within a line)
          result2 = encodeLineSegments st' ms
          rest = fst result2
          st'' = snd result2
      in if rest == "" then (seg, st')
         else (seg ++ "," ++ rest, st'')

    encodeLines : Int -> Int -> MappingState -> List (Int, List SourceMapping) -> String
    encodeLines curLine maxLine st [] =
      -- Fill remaining lines with semicolons
      if curLine <= maxLine
      then replicate (cast (maxLine - curLine)) ';'
      else ""
    encodeLines curLine maxLine st ((lineNum, lineMappings) :: rest) =
      let -- Add semicolons for empty lines before this one
          emptyLines = replicate (cast (lineNum - curLine)) ';'
          -- Encode this line's segments (reset genCol at line start)
          stReset = { prevGenCol := 0 } st
          result = encodeLineSegments stReset lineMappings
          lineStr = fst result
          st' = snd result
          -- Continue with remaining lines
          restStr = encodeLines (lineNum + 1) maxLine st' rest
      in emptyLines ++ lineStr ++ (if null rest && lineNum == maxLine then "" else ";") ++ restStr

--------------------------------------------------------------------------------
--          JSON Output
--------------------------------------------------------------------------------

||| Escape a string for JSON
jsonEscape : String -> String
jsonEscape s = fastPack $ concatMap escape (unpack s)
  where
    escape : Char -> List Char
    escape '"'  = ['\\', '"']
    escape '\\' = ['\\', '\\']
    escape '\n' = ['\\', 'n']
    escape '\r' = ['\\', 'r']
    escape '\t' = ['\\', 't']
    escape c    = [c]

||| Convert OriginDesc to source file path
originToPath : OriginDesc -> String
originToPath (PhysicalIdrSrc ident) = ModuleIdent.toPath ident ++ ".idr"
originToPath (PhysicalPkgSrc fname) = fname
originToPath (Virtual _) = "(virtual)"

||| Generate Source Map v3 JSON
||| @file - output file name
||| @sources - list of source file descriptors
||| @mappings - encoded mappings string
export
generateSourceMapJSON : (file : String) -> List OriginDesc -> String -> String
generateSourceMapJSON file sources mappingsStr =
  let sourcesList = fastConcat $ intersperse "," $ map (\o => "\"" ++ jsonEscape (originToPath o) ++ "\"") sources
  in fastConcat
       [ "{"
       , "\"version\":3,"
       , "\"file\":\"" ++ jsonEscape file ++ "\","
       , "\"sources\":[" ++ sourcesList ++ "],"
       , "\"names\":[],"
       , "\"mappings\":\"" ++ mappingsStr ++ "\""
       , "}"
       ]

||| Generate complete source map from mappings
||| @file - output JavaScript file name
||| @mappings - list of source mappings from prettyWithMappings
export
generateSourceMap : (file : String) -> List SourceMapping -> String
generateSourceMap file mappings =
  let (sources, srcIndex) = buildSourceIndex mappings
      mappingsStr = encodeMappings srcIndex mappings
  in generateSourceMapJSON file sources mappingsStr
