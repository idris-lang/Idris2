module Idris.IDEMode.SyntaxHighlight

import Core.Context
import Core.Context.Log
import Core.Directory
import Core.Metadata

import Idris.REPL
import Idris.Syntax
import Idris.IDEMode.Commands

import Data.List

import Libraries.Data.PosMap

%default total

||| Output some data using current dialog index
export
printOutput : {auto c : Ref Ctxt Defs} ->
              {auto o : Ref ROpts REPLOpts} ->
              SourceHighlight -> Core ()
printOutput highlight
  =  do opts <- get ROpts
        case idemode opts of
          REPL _ => pure ()
          IDEMode i _ f =>
            send f (Intermediate (HighlightSource [highlight]) i)

outputHighlight : {auto c : Ref Ctxt Defs} ->
                  {auto opts : Ref ROpts REPLOpts} ->
                  Highlight -> Core ()
outputHighlight hl =
  printOutput $ Full hl

lwOutputHighlight :
  {auto c : Ref Ctxt Defs} ->
  {auto opts : Ref ROpts REPLOpts} ->
  (FileName, NonEmptyFC, Decoration) -> Core ()
lwOutputHighlight (fname, nfc, decor) =
  printOutput $ Lw $ MkLwHighlight {location = cast (fname, nfc), decor}

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
         { location = cast (fname, nfc)
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
    modIdent <- ctxtPathToNS fname

    let allNames = filter ((PhysicalIdrSrc modIdent ==) . fst . fst)
                     $ toList meta.nameLocMap
    --decls <- filter (inFile fname) . tydecls <$> get MD
    --_ <- traverse outputNameSyntax allNames -- ++ decls)

    decors <- allSemanticHighlighting meta

    traverse_ {b = Unit}
         (\(nfc, decor, mn) =>
           case mn of
             Nothing => lwOutputHighlight (fname, nfc, decor)
             Just n  => outputNameSyntax  (fname, nfc, decor, n))
         (toList decors)

  pure loadResult
