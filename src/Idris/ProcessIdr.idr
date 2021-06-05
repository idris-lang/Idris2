module Idris.ProcessIdr

import Compiler.Inline

import Core.Binary
import Core.Context
import Core.Core
import Core.Context.Log
import Core.Directory
import Core.Env
import Core.Hash
import Core.Metadata
import Core.Options
import Core.Unify

import Parser.Unlit

import TTImp.Elab.Check
import TTImp.ProcessDecls
import TTImp.TTImp

import Idris.Desugar
import Idris.Desugar.Mutual
import Idris.Parser
import Idris.REPL.Common
import Idris.REPL.Opts
import Idris.Syntax
import Idris.Pretty

import Data.List
import Libraries.Data.NameMap

import System.File

%default covering

processDecls : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref MD Metadata} ->
               List PDecl -> Core (List Error)

processDecl : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto m : Ref MD Metadata} ->
              PDecl -> Core (List Error)

-- Special cases to avoid treating these big blocks as units
-- This should give us better error recovery (the whole block won't fail
-- as soon as one of the definitions fails)
processDecl (PNamespace fc ns ps)
    = withExtendedNS ns $ processDecls ps
processDecl (PMutual fc ps)
    = let (tys, defs) = splitMutual ps in
      processDecls (tys ++ defs)

processDecl decl
    = catch (do impdecls <- desugarDecl [] decl
                traverse_ (Check.processDecl [] (MkNested []) []) impdecls
                pure [])
            (\err => do giveUpConstraints -- or we'll keep trying...
                        pure [err])

processDecls decls
    = do xs <- concat <$> traverse processDecl decls
         Nothing <- checkDelayedHoles
             | Just err => pure (if null xs then [err] else xs)
         errs <- logTime ("+++ Totality check overall") getTotalityErrors
         pure (xs ++ errs)

readModule : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Syn SyntaxInfo} ->
             (full : Bool) -> -- load everything transitively (needed for REPL and compiling)
             FC ->
             (visible : Bool) -> -- Is import visible to top level module?
             (imp : ModuleIdent) -> -- Module name to import
             (as : Namespace) -> -- Namespace to import into
             Core ()
readModule full loc vis imp as
    = do defs <- get Ctxt
         let False = (imp, vis, as) `elem` map snd (allImported defs)
             | True => when vis (setVisible (miAsNamespace imp))
         Right fname <- nsToPath loc imp
               | Left err => throw err
         Just (syn, hash, more) <- readFromTTC False {extra = SyntaxInfo}
                                                  loc vis fname imp as
              | Nothing => when vis (setVisible (miAsNamespace imp)) -- already loaded, just set visibility
         extendSyn syn

         defs <- get Ctxt
         modNS <- getNS
         when vis $ setVisible (miAsNamespace imp)
         traverse_ (\ mimp =>
                       do let m = fst mimp
                          let reexp = fst (snd mimp)
                          let as = snd (snd mimp)
                          when (reexp || full) $ readModule full loc reexp m as) more
         setNS modNS

readImport : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Syn SyntaxInfo} ->
             Bool -> Import -> Core ()
readImport full imp
    = do readModule full (loc imp) True (path imp) (nameAs imp)
         addImported (path imp, reexport imp, nameAs imp)

||| Adds new import to the namespace without changing the current top-level namespace
export
addImport : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            {auto s : Ref Syn SyntaxInfo} ->
            Import -> Core ()
addImport imp
    = do topNS <- getNS
         readImport True imp
         setNS topNS

readHash : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           Import -> Core (Bool, (Namespace, Int))
readHash imp
    = do Right fname <- nsToPath (loc imp) (path imp)
               | Left err => throw err
         h <- readIFaceHash fname
         pure (reexport imp, (nameAs imp, h))

prelude : Import
prelude = MkImport (MkFC (Virtual Interactive) (0, 0) (0, 0)) False
                     (nsAsModuleIdent preludeNS) preludeNS

export
readPrelude : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Bool -> Core ()
readPrelude full
    = do readImport full prelude
         setNS mainNS

-- Import a TTC for use as the main file (e.g. at the REPL)
export
readAsMain : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Syn SyntaxInfo} ->
             (fname : String) -> Core ()
readAsMain fname
    = do Just (syn, _, more) <- readFromTTC {extra = SyntaxInfo}
                                             True EmptyFC True fname (nsAsModuleIdent emptyNS) emptyNS
              | Nothing => throw (InternalError "Already loaded")
         replNS <- getNS
         replNestedNS <- getNestedNS
         extendSyn syn

         -- Read the main file's top level imported modules, so we have access
         -- to their names (and any of their public imports)
         ustm <- get UST
         traverse_ (\ mimp =>
                       do let m = fst mimp
                          let as = snd (snd mimp)
                          readModule True emptyFC True m as
                          addImported (m, True, as)) more

         -- also load the prelude, if required, so that we have access to it
         -- at the REPL.
         when (not (noprelude !getSession)) $
              readModule True emptyFC True (nsAsModuleIdent preludeNS) preludeNS

         -- We're in the namespace from the first TTC, so use the next name
         -- from that for the fresh metavariable name generation
         -- TODO: Maybe we should record this per namespace, since this is
         -- a little bit of a hack? Or maybe that will have too much overhead.
         ust <- get UST
         put UST (record { nextName = nextName ustm } ust)

         setNS replNS
         setNestedNS replNestedNS

addPrelude : List Import -> List Import
addPrelude imps
  = if not (nsAsModuleIdent preludeNS `elem` map path imps)
       then prelude :: imps
       else imps

-- Get a file's modified time. If it doesn't exist, return 0 (that is, it
-- was last modified at the dawn of time so definitely out of date for
-- rebuilding purposes...)
modTime : String -> Core Integer
modTime fname
    = do Right f <- coreLift $ openFile fname Read
             | Left err => pure 0 -- Beginning of Time :)
         Right t <- coreLift $ fileModifiedTime f
             | Left err => do coreLift $ closeFile f
                              pure 0
         coreLift $ closeFile f
         pure (cast t)

export
readHeader : {auto c : Ref Ctxt Defs} ->
             {auto o : Ref ROpts REPLOpts} ->
             (path : String) -> (origin : ModuleIdent) -> Core Module
readHeader path origin
    = do Right res <- coreLift (readFile path)
            | Left err => throw (FileErr path err)
         -- Stop at the first :, that's definitely not part of the header, to
         -- save lexing the whole file unnecessarily
         setCurrentElabSource res -- for error printing purposes
         let Right (decor, mod) = runParserTo (PhysicalIdrSrc origin) (isLitFile path) (is ':') res (progHdr (PhysicalIdrSrc origin))
            | Left err => throw err
         pure mod

%foreign "scheme:collect"
prim__gc : Int -> PrimIO ()

gc : IO ()
gc = primIO $ prim__gc 4

export
addPublicHash : {auto c : Ref Ctxt Defs} ->
                (Bool, (Namespace, Int)) -> Core ()
addPublicHash (True, (mod, h)) = do addHash mod; addHash h
addPublicHash _ = pure ()

-- Process everything in the module; return the syntax information which
-- needs to be written to the TTC (e.g. exported infix operators)
-- Returns 'Nothing' if it didn't reload anything
processMod : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto m : Ref MD Metadata} ->
             {auto o : Ref ROpts REPLOpts} ->
             (srcf : String) -> (ttcf : String) -> (msg : Doc IdrisAnn) ->
             (sourcecode : String) -> (origin : ModuleIdent) ->
             Core (Maybe (List Error))
processMod srcf ttcf msg sourcecode origin
    = catch (do
        setCurrentElabSource sourcecode
        -- Just read the header to start with (this is to get the imports and
        -- see if we can avoid rebuilding if none have changed)
        modh <- readHeader srcf origin
        -- Add an implicit prelude import
        let imps =
             if (noprelude !getSession || moduleNS modh == nsAsModuleIdent preludeNS)
                then imports modh
                else addPrelude (imports modh)

        hs <- traverse readHash imps
        defs <- get Ctxt
        log "module.hash" 5 $ "Current hash " ++ show (ifaceHash defs)
        log "module.hash" 5 $ show (moduleNS modh) ++ " hashes:\n" ++
                show (sort (map snd hs))
        imphs <- readImportHashes ttcf
        log "module.hash" 5 $ "Old hashes from " ++ ttcf ++ ":\n" ++ show (sort imphs)

        -- If the old hashes are the same as the hashes we've just
        -- read from the imports, and the source file is older than
        -- the ttc, we can skip the rest.
        srctime <- modTime srcf
        ttctime <- modTime ttcf

        let ns = moduleNS modh

        if (sort (map snd hs) == sort imphs && srctime <= ttctime)
           then -- Hashes the same, source up to date, just set the namespace
                -- for the REPL
                do setNS (miAsNamespace ns)
                   pure Nothing
           else -- needs rebuilding
             do iputStrLn msg
                Right (decor, mod) <- logTime ("++ Parsing " ++ srcf) $
                            pure (runParser (PhysicalIdrSrc origin) (isLitFile srcf) sourcecode (do p <- prog (PhysicalIdrSrc origin); eoi; pure p))
                      | Left err => pure (Just [err])
                addSemanticDecorations decor
                initHash
                traverse_ addPublicHash (sort hs)
                resetNextVar
                when (ns /= nsAsModuleIdent mainNS) $
                      when (ns /= origin) $
                          throw (GenericMsg mod.headerLoc
                                   ("Module name " ++ show ns ++
                                    " does not match file name " ++ show srcf))

                -- read import ttcs in full here
                -- Note: We should only import .ttc - assumption is that there's
                -- a phase before this which builds the dependency graph
                -- (also that we only build child dependencies if rebuilding
                -- changes the interface - will need to store a hash in .ttc!)
                logTime "++ Reading imports" $
                   traverse_ (readImport False) imps

                -- Before we process the source, make sure the "hide_everywhere"
                -- names are set to private (TODO, maybe if we want this?)
--                 defs <- get Ctxt
--                 traverse (\x => setVisibility emptyFC x Private) (hiddenNames defs)
                setNS (miAsNamespace ns)
                errs <- logTime "++ Processing decls" $
                            processDecls (decls mod)
--                 coreLift $ gc

                logTime "++ Compile defs" $ compileAndInlineAll

                -- Save the import hashes for the imports we just read.
                -- If they haven't changed next time, and the source
                -- file hasn't changed, no need to rebuild.
                defs <- get Ctxt
                put Ctxt (record { importHashes = map snd hs } defs)
                pure (Just errs))
          (\err => pure (Just [err]))

-- Process a file. Returns any errors, rather than throwing them, because there
-- might be lots of errors collected across a whole file.
export
process : {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto o : Ref ROpts REPLOpts} ->
          Doc IdrisAnn -> FileName ->
          (moduleIdent : ModuleIdent) ->
          Core (List Error)
process buildmsg file ident
    = do Right res <- coreLift (readFile file)
               | Left err => pure [FileErr file err]
         catch (do ttcf <- getTTCFileName file "ttc"
                   Just errs <- logTime ("+ Elaborating " ++ file) $
                                   processMod file ttcf buildmsg res ident
                        | Nothing => pure [] -- skipped it
                   if isNil errs
                      then
                        do defs <- get Ctxt
                           ns <- ctxtPathToNS file
                           makeBuildDirectory ns
                           writeToTTC !(get Syn) ttcf
                           ttmf <- getTTCFileName file "ttm"
                           writeToTTM ttmf
                           pure []
                      else do pure errs)
               (\err => pure [err])
