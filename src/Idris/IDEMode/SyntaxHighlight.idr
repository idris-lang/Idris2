module Idris.IDEMode.SyntaxHighlight

import Core.Context
import Core.Context.Log
import Core.InitPrimitives
import Core.Metadata
import Core.TT

import Idris.REPL
import Idris.IDEMode.Commands

import Data.List

import Libraries.Data.PosMap

%default covering

SExpable Decoration where
  toSExp Typ = SymbolAtom "type"
  toSExp Function = SymbolAtom "function"
  toSExp Data = SymbolAtom "data"
  toSExp Keyword = SymbolAtom "keyword"
  toSExp Bound = SymbolAtom "bound"

record Highlight where
  constructor MkHighlight
  location : NonEmptyFC
  name : Name
  isImplicit : Bool
  key : String
  decor : Decoration
  docOverview : String
  typ : String
  ns : String

SExpable FC where
  toSExp (MkFC fname (startLine, startCol) (endLine, endCol))
    = SExpList [ SExpList [ SymbolAtom "filename", StringAtom fname ]
               , SExpList [ SymbolAtom "start", IntegerAtom (cast startLine + 1), IntegerAtom (cast startCol + 1) ]
               , SExpList [ SymbolAtom "end", IntegerAtom (cast endLine + 1), IntegerAtom (cast endCol) ]
               ]
  toSExp EmptyFC = SExpList []

SExpable Highlight where
  toSExp (MkHighlight loc nam impl k dec doc t ns)
    = SExpList [ toSExp $ justFC loc
               , SExpList [ SExpList [ SymbolAtom "name", StringAtom (show nam) ]
                          , SExpList [ SymbolAtom "namespace", StringAtom ns ]
                          , SExpList [ SymbolAtom "decor", toSExp dec ]
                          , SExpList [ SymbolAtom "implicit", toSExp impl ]
                          , SExpList [ SymbolAtom "key", StringAtom k ]
                          , SExpList [ SymbolAtom "doc-overview", StringAtom doc ]
                          , SExpList [ SymbolAtom "type", StringAtom t ]
                          ]
               ]

inFile : String -> (NonEmptyFC, a) -> Bool
inFile fname ((file, _, _), _) = file == fname

||| Output some data using current dialog index
export
printOutput : {auto c : Ref Ctxt Defs} ->
              {auto o : Ref ROpts REPLOpts} ->
              SExp -> Core ()
printOutput msg
  =  do opts <- get ROpts
        case idemode opts of
          REPL _ => pure ()
          IDEMode i _ f =>
            send f (SExpList [SymbolAtom "output",
                              msg, toSExp i])


outputHighlight : {auto c : Ref Ctxt Defs} ->
                  {auto opts : Ref ROpts REPLOpts} ->
                  Highlight -> Core ()
outputHighlight h =
  printOutput $ SExpList [ SymbolAtom "ok"
                         , SExpList [ SymbolAtom "highlight-source"
                                    , toSExp hlt
                                    ]
                         ]
  where
    hlt : List Highlight
    hlt = [h]

isPrimType : Constant -> Bool
isPrimType (I   x)  = False
isPrimType (BI  x)  = False
isPrimType (B8  x)  = False
isPrimType (B16 x)  = False
isPrimType (B32 x)  = False
isPrimType (B64 x)  = False
isPrimType (Str x)  = False
isPrimType (Ch  x)  = False
isPrimType (Db  x)  = False
isPrimType WorldVal = False
isPrimType IntType     = True
isPrimType IntegerType = True
isPrimType Bits8Type   = True
isPrimType Bits16Type  = True
isPrimType Bits32Type  = True
isPrimType Bits64Type  = True
isPrimType StringType  = True
isPrimType CharType    = True
isPrimType DoubleType  = True
isPrimType WorldType   = True


outputNameSyntax : {auto c : Ref Ctxt Defs} ->
                   {auto opts : Ref ROpts REPLOpts} ->
                   (NonEmptyFC, Name) -> Core ()
outputNameSyntax (nfc, name) = do
      defs <- get Ctxt
      let decor = case !(lookupCtxtExact name (gamma defs)) of
            Nothing => Bound
            Just ndef =>
               case definition ndef of
                 None => Bound  -- Surely impossible?
                 PMDef _ _ _ _ _ => Function
                 ExternDef 0 => Data
                 ExternDef (S _) => Function
                 ForeignDef 0 _ => Data
                 ForeignDef (S k) _ => Function
                 Builtin _ => Function
                 DCon _ _ _ => Data
                 TCon _ _ _ _ _ _ _ _ => Typ
                 Hole _ _ => Bound
                 BySearch _ _ _ => Bound
                 Guess _ _ _ => Bound
                 ImpBind => Bound
                 Delayed => Bound
      log "ide-mode.highlight" 20 $ "highlighting at " ++ show nfc
                                 ++ ": " ++ show name
                                 ++ "\nAs: " ++ show decor
      outputHighlight $ MkHighlight nfc name False "" decor "" "" ""

export
outputSyntaxHighlighting : {auto c : Ref Ctxt Defs} ->
                           {auto m : Ref MD Metadata} ->
                           {auto opts : Ref ROpts REPLOpts} ->
                           String ->
                           REPLResult ->
                           Core REPLResult
outputSyntaxHighlighting fname loadResult = do
  opts <- get ROpts
  when (opts.synHighlightOn) $ do
    allNames <- the (Core ?) $ filter (inFile fname) . toList . nameLocMap <$> get MD
    --  decls <- filter (inFile fname) . tydecls <$> get MD
    _ <- traverse outputNameSyntax allNames -- ++ decls)
    pure ()

  pure loadResult
