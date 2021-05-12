module Idris.IDEMode.SyntaxHighlight

import Core.Context
import Core.Context.Log
import Core.InitPrimitives
import Core.Metadata
import Core.TT

import Idris.REPL
import Idris.Syntax
import Idris.DocString
import Idris.IDEMode.Commands

import Data.List
import Data.Maybe

import Libraries.Data.PosMap

%default covering

SExpable Decoration where
  toSExp Typ      = SExpList [ SymbolAtom "decor", SymbolAtom "type"]
  toSExp Function = SExpList [ SymbolAtom "decor", SymbolAtom "function"]
  toSExp Data     = SExpList [ SymbolAtom "decor", SymbolAtom "data"]
  toSExp Keyword  = SExpList [ SymbolAtom "decor", SymbolAtom "keyword"]
  toSExp Bound    = SExpList [ SymbolAtom "decor", SymbolAtom "bound"]

record Highlight where
  constructor MkHighlight
  location : NonEmptyFC
  name : String
  isImplicit : Bool
  key : String
  decor : Decoration
  docOverview : String
  typ : String
  ns : String

SExpable FC where
  toSExp fc = case isNonEmptyFC fc of
    Just (fname , (startLine, startCol),  (endLine, endCol)) =>
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
  toSExp (MkHighlight loc nam impl k dec doc t ns)
    = SExpList [ toSExp $ justFC loc
               , SExpList [ SExpList [ SymbolAtom "name", StringAtom nam ]
                          , SExpList [ SymbolAtom "namespace", StringAtom ns ]
                          , toSExp dec
                          , SExpList [ SymbolAtom "implicit", toSExp impl ]
                          , SExpList [ SymbolAtom "key", StringAtom k ]
                          , SExpList [ SymbolAtom "doc-overview", StringAtom doc ]
                          , SExpList [ SymbolAtom "type", StringAtom t ]
                          ]
               ]

inFile : (s : String) -> (NonEmptyFC, a) -> Bool
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

lwOutputHighlight :
  {auto c : Ref Ctxt Defs} ->
  {auto opts : Ref ROpts REPLOpts} ->
  (NonEmptyFC, Decoration) -> Core ()
lwOutputHighlight (nfc,decor) =
  printOutput $ SExpList [ SymbolAtom "ok"
                         , SExpList [ SymbolAtom "highlight-source"
                                    , toSExp $ the (List _) [
                                    SExpList [ toSExp $ justFC nfc
               , SExpList [ toSExp decor]
               ]]]]



outputNameSyntax : {auto c : Ref Ctxt Defs} ->
                   {auto s : Ref Syn SyntaxInfo} ->
                   {auto opts : Ref ROpts REPLOpts} ->
                   (NonEmptyFC, Decoration, Name) -> Core ()
outputNameSyntax (nfc, decor, nm) = do
      defs <- get Ctxt
      log "ide-mode.highlight" 20 $ "highlighting at " ++ show nfc
                                 ++ ": " ++ show nm
                                 ++ "\nAs: " ++ show decor
      let fc = justFC nfc
      let (mns, name) = displayName nm
      outputHighlight $ MkHighlight
         { location = nfc
         , name
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
    let allNames = filter (inFile fname) $ toList meta.nameLocMap
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
             Nothing => lwOutputHighlight (nfc, decor)
             Just n  => outputNameSyntax  (nfc, decor, n))
         (defaults ++ aliases ++ toList semHigh)

  pure loadResult
