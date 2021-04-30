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
  name : Name
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
               , SExpList [ SExpList [ SymbolAtom "name", StringAtom (show nam) ]
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
outputNameSyntax (nfc, decor, name) = do
      defs <- get Ctxt
      log "ide-mode.highlight" 20 $ "highlighting at " ++ show nfc
                                 ++ ": " ++ show name
                                 ++ "\nAs: " ++ show decor
      let fc = justFC nfc
      outputHighlight $ MkHighlight
         { location = nfc
         , name
         , isImplicit = False
         , key = ""
         , decor
         , docOverview = "" --!(getDocsForName fc name)
         , typ = "" -- TODO: extract type maybe "" show !(lookupTyExact name (gamma defs))
         , ns = "" --TODO: extract namespace
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
    log "ide-mode.highlight" 19 $ "Semantic metadata is: " ++ show meta.semanticHighlighting
    traverse_ {b = Unit}
         (\(nfc, decor, mn) =>
           case mn of
             Nothing => lwOutputHighlight (nfc, decor)
             Just n  => outputNameSyntax  (nfc, decor, n))
         (toList meta.semanticHighlighting)
  pure loadResult
