module Idris.IDEMode.SyntaxHighlight

import Core.Context
import Core.Context.Log
import Core.Directory
import Core.Metadata

import Idris.REPL
import Idris.Syntax
import Idris.Pretty
import Idris.Doc.String
import Idris.IDEMode.Commands

import Data.List

import Libraries.Data.PosMap

%default total

------------------------------------------------------------------------
-- Text properties supported by the IDE mode
------------------------------------------------------------------------

data Formatting : Type where
  Bold      : Formatting
  Italic    : Formatting
  Underline : Formatting

-- CAREFUL: this instance is used in SExpable Formatting. If you change
-- it then you need to fix the SExpable implementation in order not to
-- break the IDE mode.
Show Formatting where
  show Bold = "bold"
  show Italic = "italic"
  show Underline = "underline"

-- At most one decoration & one formatting
-- (We could use `These` to guarantee non-emptiness but I am not
-- convinced this will stay being just 2 fields e.g. the emacs mode
-- has support for tagging things as errors, adding links, etc.)
public export
record Properties where
  constructor MkProperties
  decor  : Maybe Decoration
  format : Maybe Formatting

export
mkDecor : Decoration -> Properties
mkDecor dec = MkProperties (Just dec) Nothing

export
mkFormat : Formatting -> Properties
mkFormat = MkProperties Nothing . Just

export
syntaxToProperties : IdrisSyntax -> Maybe Properties
syntaxToProperties syn = mkDecor <$> syntaxToDecoration syn

export
annToProperties : IdrisAnn -> Maybe Properties
annToProperties Warning       = Nothing
annToProperties Error         = Nothing
annToProperties ErrorDesc     = Nothing
annToProperties FileCtxt      = Nothing
annToProperties Code          = Nothing
annToProperties Meta          = Nothing
annToProperties (Syntax syn)  = syntaxToProperties syn
annToProperties UserDocString = Nothing

export
docToProperties : IdrisDocAnn -> Maybe Properties
docToProperties Header        = pure $ mkFormat Underline
docToProperties Deprecation   = pure $ mkFormat Bold
docToProperties Declarations  = Nothing
docToProperties (Decl _)      = Nothing
docToProperties DocStringBody = Nothing
docToProperties UserDocString = Nothing
docToProperties (Syntax syn)  = syntaxToProperties syn

SExpable Decoration where
  toSExp decor = SExpList [ SymbolAtom "decor"
                          , SymbolAtom (show decor)
                          ]

SExpable Formatting where
  toSExp format = SExpList [ SymbolAtom "text-formatting"
                           , SymbolAtom (show format)
                           ]

export
SExpable Properties where
  toSExp (MkProperties dec form)  = SExpList $ catMaybes
    [ toSExp <$> form
    , toSExp <$> dec
    ]


record Highlight where
  constructor MkHighlight
  location : NonEmptyFC
  filename : String
  name : String
  isImplicit : Bool
  key : String
  decor : Decoration
  docOverview : String
  typ : String
  ns : String

SExpable (FileName, FC) where
  toSExp (fname, fc) = case isNonEmptyFC fc of
    Just (origin, (startLine, startCol), (endLine, endCol)) =>
      SExpList [ SExpList [ SymbolAtom "filename", StringAtom fname ]
               , SExpList [ SymbolAtom "start"
                          , IntegerAtom (cast startLine + 1)
                          , IntegerAtom (cast startCol + 1)
                          ]
               , SExpList [ SymbolAtom "end"
                          , IntegerAtom (cast endLine + 1)
                          , IntegerAtom (cast endCol)
                          ]
               ]
    Nothing => SExpList []

SExpable Highlight where
  toSExp (MkHighlight loc fname nam impl k dec doc t ns)
    = SExpList [ toSExp $ (fname, justFC loc)
               , SExpList [ SExpList [ SymbolAtom "name", StringAtom nam ]
                          , SExpList [ SymbolAtom "namespace", StringAtom ns ]
                          , toSExp dec
                          , SExpList [ SymbolAtom "implicit", toSExp impl ]
                          , SExpList [ SymbolAtom "key", StringAtom k ]
                          , SExpList [ SymbolAtom "doc-overview", StringAtom doc ]
                          , SExpList [ SymbolAtom "type", StringAtom t ]
                          ]
               ]

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

lwOutputHighlight :
  {auto c : Ref Ctxt Defs} ->
  {auto opts : Ref ROpts REPLOpts} ->
  (FileName, NonEmptyFC, Decoration) -> Core ()
lwOutputHighlight (fname, nfc, decor) =
  printOutput $ SExpList [ SymbolAtom "ok"
                         , SExpList [ SymbolAtom "highlight-source"
                                    , toSExp $ the (List _) [
                                    SExpList [ toSExp $ (fname, justFC nfc)
               , SExpList [ toSExp decor]
               ]]]]



outputNameSyntax : {auto c : Ref Ctxt Defs} ->
                   {auto s : Ref Syn SyntaxInfo} ->
                   {auto opts : Ref ROpts REPLOpts} ->
                   (FileName, NonEmptyFC, Decoration, Name) -> Core ()
outputNameSyntax (fname, nfc, decor, nm) = do
      defs <- get Ctxt
      log "ide-mode.highlight" 20 $ "highlighting at " ++ show nfc
                                 ++ ": " ++ show nm
                                 ++ "\nAs: " ++ show decor
      let fc = justFC nfc
      let (mns, name) = displayName nm
      outputHighlight $ MkHighlight
         { location = nfc
         , name
         , filename = fname
         , isImplicit = False
         , key = ""
         , decor
         , docOverview = "" --!(getDocsForName fc nm)
         , typ = "" -- TODO: extract type maybe "" show !(lookupTyExact nm (gamma defs))
         , ns = maybe "" show mns
         }

export
outputSyntaxHighlighting : {auto c : Ref Ctxt Defs} ->
                           {auto m : Ref MD Metadata} ->
                           {auto s : Ref Syn SyntaxInfo} ->
                           {auto opts : Ref ROpts REPLOpts} ->
                           String ->
                           REPLResult ->
                           Core REPLResult
outputSyntaxHighlighting fname loadResult = do
  opts <- get ROpts
  when (opts.synHighlightOn) $ do
    meta <- get MD
    modIdent <- ctxtPathToNS fname

    let allNames = filter ((PhysicalIdrSrc modIdent ==) . fst . fst)
                     $ toList meta.nameLocMap
    --decls <- filter (inFile fname) . tydecls <$> get MD
    --_ <- traverse outputNameSyntax allNames -- ++ decls)

    let semHigh = meta.semanticHighlighting
    log "ide-mode.highlight" 19 $
      "Semantic metadata is: " ++ show semHigh

    let aliases
          : List ASemanticDecoration
          = flip foldMap meta.semanticAliases $ \ (from, to) =>
              let decors = uncurry exactRange (snd to) semHigh in
              map (\ ((fnm, loc), rest) => ((fnm, snd from), rest)) decors
    log "ide-mode.highlight.alias" 19 $
      "Semantic metadata from aliases is: " ++ show aliases

    let defaults
         : List ASemanticDecoration
         = flip foldMap meta.semanticDefaults $ \ decor@((_, range), _) =>
             case uncurry exactRange range semHigh of
               [] => [decor]
               _ => []

    traverse_ {b = Unit}
         (\(nfc, decor, mn) =>
           case mn of
             Nothing => lwOutputHighlight (fname, nfc, decor)
             Just n  => outputNameSyntax  (fname, nfc, decor, n))
         (defaults ++ aliases ++ toList semHigh)

  pure loadResult
