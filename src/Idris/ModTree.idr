module Idris.ModTree

import Core.Binary
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Directory
import Core.Metadata
import Core.Options
import Core.InitPrimitives
import Core.UnifyState

import Idris.Parser
import Idris.ProcessIdr
import Idris.REPL.Common
import Idris.Syntax
import Idris.Pretty

import Data.List
import Data.Either
import Data.String

import System.Directory

import Libraries.Data.StringMap
import Libraries.Data.String.Extra as Extra

%default covering

record ModTree where
  constructor MkModTree
  nspace : ModuleIdent
  sourceFile : Maybe String
  deps : List ModTree

covering
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
                              modInfo <- readHeader file mod
                              let imps = map path (imports modInfo)
                              if mod `elem` imps
                                then coreFail $ CyclicImports [mod, mod]
                                else do
                                  ms <- traverse (mkModTree loc (mod :: done) Nothing) imps
                                  let mt = MkModTree mod (Just file) ms
                                  update AllMods ((mod, mt) ::)
                                  pure mt
                         Just m => pure m)
                -- Couldn't find source, assume it's in a package directory
                (\err =>
                    case err of
                         CyclicImports _ => throw err
                         ParseFail _ => throw err
                         LexFail _ _ => throw err
                         LitFail _ => throw err
                         _ => pure (MkModTree mod Nothing []))

data DoneMod : Type where
data BuildOrder : Type where

-- Given a module tree, returns the modules in the reverse order they need to
-- be built, including their dependencies
mkBuildMods : {auto d : Ref DoneMod (StringMap ())} ->
              {auto o : Ref BuildOrder (List BuildMod)} ->
              ModTree -> Core ()
mkBuildMods mod
    = whenJust (sourceFile mod) $ \ sf =>
            do done <- get DoneMod
               case lookup sf done of
                    Just _ => pure ()
                    Nothing =>
                       do -- build dependencies
                          traverse_ mkBuildMods (deps mod)
                          -- build it now
                          update BuildOrder
                                   (MkBuildMod sf mod.nspace
                                               (map nspace mod.deps) ::)
                          update DoneMod $ insert sf ()

-- Given a main file name, return the list of modules that need to be
-- built for that main file, in the order they need to be built
-- Return an empty list if it turns out it's in the 'done' list
export
getBuildMods : {auto c : Ref Ctxt Defs} ->
               {auto o : Ref ROpts REPLOpts} ->
               FC -> (done : List BuildMod) ->
               (mainFile : String) ->
               Core (List BuildMod)
getBuildMods loc done fname
    = do a <- newRef AllMods []
         fname_ns <- ctxtPathToNS fname
         if fname_ns `elem` map buildNS done
            then pure []
            else
              do t <- mkModTree {a} loc [] (Just fname) fname_ns
                 dm <- newRef DoneMod empty
                 o <- newRef BuildOrder []
                 mkBuildMods {d=dm} {o} t
                 pure (reverse !(get BuildOrder))

checkTotalReq : {auto c : Ref Ctxt Defs} ->
                String -> String -> TotalReq -> Core Bool
checkTotalReq sourceFile ttcFile expected
  = catch (do log "totality.requirement" 20 $
                "Reading totalReq from " ++ ttcFile
              Just got <- readTotalReq ttcFile
                | Nothing => pure False
              log "totality.requirement" 20 $ unwords
                [ "Got", show got, "and expected", show expected ++ ":"
                , "we", ifThenElse (got < expected) "should" "shouldn't"
                , "rebuild" ]
              -- if what we got (i.e. what we used when we checked the file the
              -- first time around) was strictly less stringent than what we
              -- expect now then we need to rebuild.
              pure (got < expected))
          (\error => pure False)

needsBuildingTime : {auto c : Ref Ctxt Defs} ->
                    (sourceFile : String) -> (ttcFile : String) ->
                    (depFiles : List String) -> Core Bool
needsBuildingTime sourceFile ttcFile depFiles
  = isTTCOutdated ttcFile (sourceFile :: depFiles)

needsBuildingDepHash : {auto c : Ref Ctxt Defs} ->
                 String -> Core Bool
needsBuildingDepHash depFileName
  = catch (do defs                   <- get Ctxt
              depTTCFileName         <- getTTCFileName depFileName "ttc"
              not <$> unchangedHash defs.options.hashFn depTTCFileName depFileName)
          (\error => pure False)

||| Build from source if any of the dependencies, or the associated source file,
||| have been modified from the stored hashes.
needsBuildingHash : {auto c : Ref Ctxt Defs} ->
                    (sourceFile : String) -> (ttcFile : String) ->
                    (depFiles : List String) -> Core Bool
needsBuildingHash sourceFile ttcFile depFiles
  = do defs                <- get Ctxt
       sourceUnchanged <- unchangedHash defs.options.hashFn ttcFile sourceFile
       depFilesHashDiffers <- any id <$> traverse needsBuildingDepHash depFiles
       pure $ (not sourceUnchanged) || depFilesHashDiffers

export
needsBuilding :
  {auto c : Ref Ctxt Defs} ->
  {auto o : Ref ROpts REPLOpts} ->
  (sourceFile, ttcFile : String) -> List String -> Core Bool
needsBuilding sourceFile ttcFile depFiles
  = do -- if the ttc file does not exist there is no point in asking
       -- whether we need to rebuild it
       True <- coreLift $ exists ttcFile
         | False => pure True
       -- check if hash match
       checkHashesInsteadOfTime <- checkHashesInsteadOfModTime <$> getSession
       False <- ifThenElse checkHashesInsteadOfTime
                           needsBuildingHash
                           needsBuildingTime
                  sourceFile ttcFile depFiles
         | True => pure True

       log "import" 20 $ "\{ifThenElse checkHashesInsteadOfTime "Hashes" "Mod Times"} still valid for " ++ sourceFile

       False <- missingIncremental ttcFile
         | True => pure True

       -- in case we're loading the main file, make sure the TTC is
       -- using the appropriate default totality requirement
       Just f <- mainfile <$> get ROpts
         | Nothing => pure False
       log "totality.requirement" 10 $ concat {t = List}
         [ "Checking totality requirement of "
         , sourceFile
         , " (main file is "
         , f
         , ")"
         ]
       let True = sourceFile == f
         | False => pure False
       True <- checkTotalReq sourceFile ttcFile !(totalReq <$> getSession)
         | False => pure False
       -- if it needs rebuilding then remove the buggy .ttc file to avoid going
       -- into an infinite loop!
       Right () <- coreLift $ removeFile ttcFile
         | Left err => throw (FileErr ttcFile err)
       pure True


buildMod : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           FC -> Nat -> Nat -> BuildMod ->
           Core (List Error)
buildMod loc num len mod
   = do clearCtxt; addPrimitives
        lazyActive True; setUnboundImplicits True

        let sourceFile = buildFile mod
        let modNamespace = buildNS mod
        ttcFile <- getTTCFileName sourceFile "ttc"
        -- We'd expect any errors in nsToPath to have been caught by now
        -- since the imports have been built! But we still have to check.
        depFilesE <- traverse (nsToPath loc) (imports mod)
        let (ferrs, depFiles) = partitionEithers depFilesE

        log "import" 20 $ unwords $
          [ "Checking whether to rebuild "
          , sourceFile
          , "(" ++ ttcFile ++ ")"
          , "with dependencies:"
          ] ++ depFiles
        rebuild <- needsBuilding sourceFile ttcFile depFiles

        u <- newRef UST initUState
        m <- newRef MD (initMetadata (PhysicalIdrSrc modNamespace))
        put Syn initSyntax

        errs <- ifThenElse (not rebuild) (pure []) $
           do let pad = minus (length $ show len) (length $ show num)
              let msgPrefix : Doc IdrisAnn
                  = pretty0 (replicate pad ' ') <+> byShow num
                    <+> slash <+> byShow len <+> colon
              let buildMsg : Doc IdrisAnn
                  = pretty0 mod.buildNS
                    <++> parens (pretty0 sourceFile)
              log "import.file" 10 $ "Processing " ++ sourceFile
              process {u} {m} msgPrefix buildMsg sourceFile modNamespace

        ws <- emitWarningsAndErrors (if null errs then ferrs else errs)
        pure (ws ++ if null errs then ferrs else ferrs ++ errs)

export
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
    = do mods <- getBuildMods EmptyFC [] fname
         log "import" 20 $ "Needs to rebuild: " ++ show mods
         ok <- buildMods EmptyFC 1 (length mods) mods
         case ok of
              [] => do -- On success, reload the main ttc in a clean context
                       clearCtxt; addPrimitives
                       modIdent <- ctxtPathToNS fname
                       put MD (initMetadata (PhysicalIdrSrc modIdent))
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
    = do mods <- getAllBuildMods EmptyFC [] allFiles
         -- There'll be duplicates, so if something is already built, drop it
         let mods' = dropLater mods
         buildMods EmptyFC 1 (length mods') mods'
  where
    dropLater : List BuildMod -> List BuildMod
    dropLater [] = []
    dropLater (b :: bs)
        = b :: dropLater (filter (\x => buildFile x /= buildFile b) bs)
