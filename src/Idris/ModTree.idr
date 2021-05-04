module Idris.ModTree

import Core.Binary
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Directory
import Core.Metadata
import Core.Options
import Core.Primitives
import Core.InitPrimitives
import Core.UnifyState

import Idris.Desugar
import Idris.Error
import Idris.Parser
import Idris.ProcessIdr
import Idris.REPL.Common
import Idris.Syntax
import Idris.Pretty

import Data.List
import Libraries.Data.StringMap

import System.Directory
import System.File

import Libraries.Utils.Either

%default covering

record ModTree where
  constructor MkModTree
  nspace : ModuleIdent
  sourceFile : Maybe String
  deps : List ModTree

Show ModTree where
  show t = show (sourceFile t) ++ " " ++ show (nspace t) ++ "<-" ++ show (deps t)

-- A module file to build, and its list of dependencies
-- From this we can work out if the source file needs rebuilding, assuming
-- things are build in dependency order. A source file needs rebuilding
-- if:
--  + Its corresponding ttc is older than the source file
--  + Any of the import ttcs are *newer* than the corresponding ttc
--    (If so: also any imported ttc's fingerprint is different from the one
--    stored in the source file's ttc)
public export
record BuildMod where
  constructor MkBuildMod
  buildFile : String
  buildNS : ModuleIdent
  imports : List ModuleIdent

export
Show BuildMod where
  show t = buildFile t ++ " [" ++ showSep ", " (map show (imports t)) ++ "]"

data AllMods : Type where

mkModTree : {auto c : Ref Ctxt Defs} ->
            {auto o : Ref ROpts REPLOpts} ->
            {auto a : Ref AllMods (List (ModuleIdent, ModTree))} ->
            FC ->
            (done : List ModuleIdent) -> -- if 'mod' is here we have a cycle
            (modFP : Maybe FileName) -> -- Sometimes we know already know what the file name is
            (mod : ModuleIdent) ->      -- Otherwise we'll compute it from the module name
            Core ModTree
mkModTree loc done modFP mod
  = if mod `elem` done
       then throw (CyclicImports (done ++ [mod]))
       else
          -- Read imports from source file. If the source file isn't
          -- available, it's not our responsibility
          catch (do all <- get AllMods
                    -- If we've seen it before, reuse what we found
                    case lookup mod all of
                         Nothing =>
                           do file <- maybe (nsToSource loc mod) pure modFP
                              modInfo <- readHeader file
                              let imps = map path (imports modInfo)
                              ms <- traverse (mkModTree loc (mod :: done) Nothing) imps
                              let mt = MkModTree mod (Just file) ms
                              all <- get AllMods
                              put AllMods ((mod, mt) :: all)
                              pure mt
                         Just m => pure m)
                -- Couldn't find source, assume it's in a package directory
                (\err =>
                    case err of
                         CyclicImports _ => throw err
                         ParseFail _ _ => throw err
                         _ => pure (MkModTree mod Nothing []))

data DoneMod : Type where
data BuildOrder : Type where

-- Given a module tree, returns the modules in the reverse order they need to
-- be built, including their dependencies
mkBuildMods : {auto d : Ref DoneMod (StringMap ())} ->
              {auto o : Ref BuildOrder (List BuildMod)} ->
              ModTree -> Core ()
mkBuildMods mod
    = maybe (pure ())
         (\sf =>
            do done <- get DoneMod
               case lookup sf done of
                    Just _ => pure ()
                    Nothing =>
                       do -- build dependencies
                          traverse_ mkBuildMods (deps mod)
                          -- build it now
                          bo <- get BuildOrder
                          put BuildOrder
                                (MkBuildMod sf (nspace mod)
                                            (map nspace (deps mod)) :: bo)
                          done <- get DoneMod
                          put DoneMod (insert sf () done))
         (sourceFile mod)

-- Given a main file name, return the list of modules that need to be
-- built for that main file, in the order they need to be built
-- Return an empty list if it turns out it's in the 'done' list
getBuildMods : {auto c : Ref Ctxt Defs} ->
               {auto o : Ref ROpts REPLOpts} ->
               FC -> (done : List BuildMod) ->
               (mainFile : String) ->
               Core (List BuildMod)
getBuildMods loc done fname
    = do a <- newRef AllMods []
         d <- getDirs
         fname_ns <- pathToNS (working_dir d) (source_dir d) fname
         if fname_ns `elem` map buildNS done
            then pure []
            else
              do t <- mkModTree {a} loc [] (Just fname) fname_ns
                 dm <- newRef DoneMod empty
                 o <- newRef BuildOrder []
                 mkBuildMods {d=dm} {o} t
                 pure (reverse !(get BuildOrder))

fnameModified : String -> Core Integer
fnameModified fname
    = do Right f <- coreLift $ openFile fname Read
             | Left err => throw (FileErr fname err)
         Right t <- coreLift $ fileModifiedTime f
             | Left err => do coreLift $ closeFile f
                              throw (FileErr fname err)
         coreLift $ closeFile f
         pure (cast t)

buildMod : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           FC -> Nat -> Nat -> BuildMod ->
           Core (List Error)
-- Build from source if any of the dependencies, or the associated source
-- file, have a modification time which is newer than the module's ttc
-- file
buildMod loc num len mod
   = do clearCtxt; addPrimitives
        lazyActive True; setUnboundImplicits True
        let src = buildFile mod
        mttc <- getTTCFileName src "ttc"
        -- We'd expect any errors in nsToPath to have been caught by now
        -- since the imports have been built! But we still have to check.
        depFilesE <- traverse (nsToPath loc) (imports mod)
        let (ferrs, depFiles) = partitionEithers depFilesE
        ttcTime <- catch (do t <- fnameModified mttc
                             pure (Just t))
                         (\err => pure Nothing)
        srcTime <- fnameModified src
        depTimes <- traverse (\f => do t <- fnameModified f
                                       pure (f, t)) depFiles
        let needsBuilding =
               case ttcTime of
                    Nothing => True
                    Just t => any (\x => x > t) (srcTime :: map snd depTimes)
        u <- newRef UST initUState
        m <- newRef MD initMetadata
        put Syn initSyntax

        if needsBuilding
           then do let msg : Doc IdrisAnn = pretty num <+> slash <+> pretty len <+> colon
                               <++> pretty "Building" <++> pretty mod.buildNS <++> parens (pretty src)
                   [] <- process {u} {m} msg src
                      | errs => do emitWarnings
                                   traverse_ emitError errs
                                   pure (ferrs ++ errs)
                   emitWarnings
                   traverse_ emitError ferrs
                   pure ferrs
           else do emitWarnings
                   traverse_ emitError ferrs
                   pure ferrs

buildMods : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto o : Ref ROpts REPLOpts} ->
            FC -> Nat -> Nat -> List BuildMod ->
            Core (List Error)
buildMods fc num len [] = pure []
buildMods fc num len (m :: ms)
    = case !(buildMod fc num len m) of
           [] => buildMods fc (1 + num) len ms
           errs => pure errs

export
buildDeps : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto o : Ref ROpts REPLOpts} ->
            (mainFile : String) ->
            Core (List Error)
buildDeps fname
    = do mods <- getBuildMods toplevelFC [] fname
         ok <- buildMods toplevelFC 1 (length mods) mods
         case ok of
              [] => do -- On success, reload the main ttc in a clean context
                       clearCtxt; addPrimitives
                       put MD initMetadata
                       mainttc <- getTTCFileName fname "ttc"
                       log "import" 10 $ "Reloading " ++ show mainttc ++ " from " ++ fname
                       readAsMain mainttc

                       -- Load the associated metadata for interactive editing
                       mainttm <- getTTCFileName fname "ttm"
                       log "import" 10 $ "Reloading " ++ show mainttm
                       readFromTTM mainttm
                       pure []
              errs => pure errs -- Error happened, give up

getAllBuildMods : {auto c : Ref Ctxt Defs} ->
                  {auto s : Ref Syn SyntaxInfo} ->
                  {auto o : Ref ROpts REPLOpts} ->
                  FC -> (done : List BuildMod) ->
                  (allFiles : List String) ->
                  Core (List BuildMod)
getAllBuildMods fc done [] = pure done
getAllBuildMods fc done (f :: fs)
    = do ms <- getBuildMods fc done f
         getAllBuildMods fc (ms ++ done) fs

export
buildAll : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           (allFiles : List String) ->
           Core (List Error)
buildAll allFiles
    = do mods <- getAllBuildMods toplevelFC [] allFiles
         -- There'll be duplicates, so if something is already built, drop it
         let mods' = dropLater mods
         buildMods toplevelFC 1 (length mods') mods'
  where
    dropLater : List BuildMod -> List BuildMod
    dropLater [] = []
    dropLater (b :: bs)
        = b :: dropLater (filter (\x => buildFile x /= buildFile b) bs)
