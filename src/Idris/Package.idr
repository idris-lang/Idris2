module Idris.Package

import Compiler.Common

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Directory
import Core.Metadata
import Core.Name.Namespace
import Core.Options
import Core.Unify

import Data.List
import Data.Maybe
import Data.SnocList
import Data.String
import Data.These

import Parser.Package
import System
import System.Directory
import Libraries.System.Directory.Tree
import System.File

import Libraries.Data.SortedMap
import Libraries.Data.StringMap
import Libraries.Data.StringTrie
import Libraries.Text.Parser
import Libraries.Utils.Path
import Libraries.Text.PrettyPrint.Prettyprinter.Render.String

import Idris.CommandLine
import Idris.Doc.HTML
import Idris.Doc.String
import Idris.ModTree
import Idris.Pretty
import Idris.ProcessIdr
import Idris.REPL
import Idris.REPL.Common
import Idris.REPL.Opts
import Idris.SetOptions
import Idris.Syntax
import Idris.Version

import public Idris.Package.Types
import Idris.Package.Init

%default covering

installDir : PkgDesc -> String
installDir p = name p
            ++ "-"
            ++ show (fromMaybe (MkPkgVersion (0 ::: [])) (version p))

data DescField  : Type where
  PVersion      : FC -> PkgVersion -> DescField
  PLangVersions : FC -> PkgVersionBounds -> DescField
  PVersionDep   : FC -> String -> DescField
  PAuthors      : FC -> String -> DescField
  PMaintainers  : FC -> String -> DescField
  PLicense      : FC -> String -> DescField
  PBrief        : FC -> String -> DescField
  PReadMe       : FC -> String -> DescField
  PHomePage     : FC -> String -> DescField
  PSourceLoc    : FC -> String -> DescField
  PBugTracker   : FC -> String -> DescField
  PDepends      : List Depends -> DescField
  PModules      : List (FC, ModuleIdent) -> DescField
  PMainMod      : FC -> ModuleIdent -> DescField
  PExec         : String -> DescField
  POpts         : FC -> String -> DescField
  PSourceDir    : FC -> String -> DescField
  PBuildDir     : FC -> String -> DescField
  POutputDir    : FC -> String -> DescField
  PPrebuild     : FC -> String -> DescField
  PPostbuild    : FC -> String -> DescField
  PPreinstall   : FC -> String -> DescField
  PPostinstall  : FC -> String -> DescField
  PPreclean     : FC -> String -> DescField
  PPostclean    : FC -> String -> DescField

field : String -> Rule DescField
field fname
      = strField PAuthors "authors"
    <|> strField PMaintainers "maintainers"
    <|> strField PLicense "license"
    <|> strField PBrief "brief"
    <|> strField PReadMe "readme"
    <|> strField PHomePage "homepage"
    <|> strField PSourceLoc "sourceloc"
    <|> strField PBugTracker "bugtracker"
    <|> strField POpts "options"
    <|> strField POpts "opts"
    <|> strField PSourceDir "sourcedir"
    <|> strField PBuildDir "builddir"
    <|> strField POutputDir "outputdir"
    <|> strField PPrebuild "prebuild"
    <|> strField PPostbuild "postbuild"
    <|> strField PPreinstall "preinstall"
    <|> strField PPostinstall "postinstall"
    <|> strField PPreclean "preclean"
    <|> strField PPostclean "postclean"
    <|> do start <- location
           ignore $ exactProperty "version"
           equals
           vs <- sepBy1 dot' integerLit
           end <- location
           pure (PVersion (MkFC (PhysicalPkgSrc fname) start end)
                          (MkPkgVersion (fromInteger <$> vs)))
    <|> do start <- location
           ignore $ exactProperty "langversion"
           lvs <- langversions
           end <- location
           pure (PLangVersions (MkFC (PhysicalPkgSrc fname) start end) lvs)
    <|> do start <- location
           ignore $ exactProperty "version"
           equals
           v <- stringLit
           end <- location
           pure (PVersionDep (MkFC (PhysicalPkgSrc fname) start end) v)
    <|> do ignore $ exactProperty "depends"
           equals
           ds <- sep depends
           pure (PDepends ds)
    <|> do ignore $ exactProperty "modules"
           equals
           ms <- sep (do start <- location
                         m <- moduleIdent
                         end <- location
                         pure (MkFC (PhysicalPkgSrc fname) start end, m))
           pure (PModules ms)
    <|> do ignore $ exactProperty "main"
           equals
           start <- location
           m <- moduleIdent
           end <- location
           pure (PMainMod (MkFC (PhysicalPkgSrc fname) start end) m)
    <|> do ignore $ exactProperty "executable"
           equals
           e <- (stringLit <|> packageName)
           pure (PExec e)
  where
    data Bound = LT PkgVersion Bool | GT PkgVersion Bool

    bound : Rule (List Bound)
    bound
        = do lte
             vs <- sepBy1 dot' integerLit
             pure [LT (MkPkgVersion (fromInteger <$> vs)) True]
      <|> do gte
             vs <- sepBy1 dot' integerLit
             pure [GT (MkPkgVersion (fromInteger <$> vs)) True]
      <|> do lt
             vs <- sepBy1 dot' integerLit
             pure [LT (MkPkgVersion (fromInteger <$> vs)) False]
      <|> do gt
             vs <- sepBy1 dot' integerLit
             pure [GT (MkPkgVersion (fromInteger <$> vs)) False]
      <|> do eqop
             vs <- sepBy1 dot' integerLit
             pure [LT (MkPkgVersion (fromInteger <$> vs)) True,
                   GT (MkPkgVersion (fromInteger <$> vs)) True]

    mkBound : List Bound -> PkgVersionBounds -> EmptyRule PkgVersionBounds
    mkBound (LT b i :: bs) pkgbs
        = maybe (mkBound bs ({ upperBound := Just b,
                               upperInclusive := i } pkgbs))
                (\_ => fail "Dependency already has an upper bound")
                pkgbs.upperBound
    mkBound (GT b i :: bs) pkgbs
        = maybe (mkBound bs ({ lowerBound := Just b,
                               lowerInclusive := i } pkgbs))
                (\_ => fail "Dependency already has a lower bound")
                pkgbs.lowerBound
    mkBound [] pkgbs = pure pkgbs

    langversions : EmptyRule PkgVersionBounds
    langversions
        = do bs <- sepBy andop bound
             mkBound (concat bs) anyBounds

    depends : Rule Depends
    depends
        = do name <- packageName
             bs <- sepBy andop bound
             pure (MkDepends name !(mkBound (concat bs) anyBounds))

    strField : (FC -> String -> DescField) -> String -> Rule DescField
    strField fieldConstructor fieldName
        = do start <- location
             ignore $ exactProperty fieldName
             equals
             str <- stringLit
             end <- location
             pure $ fieldConstructor (MkFC (PhysicalPkgSrc fname) start end) str

parsePkgDesc : String -> Rule (String, List DescField)
parsePkgDesc fname
    = do ignore $ exactProperty "package"
         name <- packageName
         fields <- many (field fname)
         pure (name, fields)

data ParsedMods : Type where

data MainMod : Type where

addField : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           {auto p : Ref ParsedMods (List (FC, ModuleIdent))} ->
           {auto m : Ref MainMod (Maybe (FC, ModuleIdent))} ->
           DescField -> PkgDesc -> Core PkgDesc
addField (PVersion fc n)       pkg = pure $ { version := Just n } pkg
addField (PLangVersions fc bs) pkg = pure $ { langversion := Just bs } pkg
addField (PVersionDep fc n)   pkg
    = do emitWarning (Deprecated "version numbers must now be of the form x.y.z" Nothing)
         pure pkg
addField (PAuthors fc a)     pkg = pure $ { authors := Just a } pkg
addField (PMaintainers fc a) pkg = pure $ { maintainers := Just a } pkg
addField (PLicense fc a)     pkg = pure $ { license := Just a } pkg
addField (PBrief fc a)       pkg = pure $ { brief := Just a } pkg
addField (PReadMe fc a)      pkg = pure $ { readme := Just a } pkg
addField (PHomePage fc a)    pkg = pure $ { homepage := Just a } pkg
addField (PSourceLoc fc a)   pkg = pure $ { sourceloc := Just a } pkg
addField (PBugTracker fc a)  pkg = pure $ { bugtracker := Just a } pkg
addField (PDepends ds)       pkg = pure $ { depends := ds } pkg
-- we can't resolve source files for modules without knowing the source directory,
-- so we save them for the second pass
addField (PModules ms)       pkg = do put ParsedMods ms
                                      pure pkg
addField (PMainMod loc n)    pkg = do put MainMod (Just (loc, n))
                                      pure pkg
addField (PExec e)           pkg = pure $ { executable := Just e } pkg
addField (POpts fc e)        pkg = pure $ { options := Just (fc, e) } pkg
addField (PSourceDir fc a)   pkg = pure $ { sourcedir := Just a } pkg
addField (PBuildDir fc a)    pkg = pure $ { builddir := Just a } pkg
addField (POutputDir fc a)   pkg = pure $ { outputdir := Just a } pkg
addField (PPrebuild fc e)    pkg = pure $ { prebuild := Just (fc, e) } pkg
addField (PPostbuild fc e)   pkg = pure $ { postbuild := Just (fc, e) } pkg
addField (PPreinstall fc e)  pkg = pure $ { preinstall := Just (fc, e) } pkg
addField (PPostinstall fc e) pkg = pure $ { postinstall := Just (fc, e) } pkg
addField (PPreclean fc e)    pkg = pure $ { preclean := Just (fc, e) } pkg
addField (PPostclean fc e)   pkg = pure $ { postclean := Just (fc, e) } pkg

addFields : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto o : Ref ROpts REPLOpts} ->
            (setSrc : Bool) ->
            List DescField -> PkgDesc -> Core PkgDesc
addFields setSrc xs desc = do
  p <- newRef ParsedMods []
  m <- newRef MainMod Nothing
  added <- go {p} {m} xs desc
  when setSrc $ setSourceDir (sourcedir added)
  ms <- get ParsedMods
  mmod <- get MainMod
  pure $
    { modules := !(traverse toSource ms)
    , mainmod := !(traverseOpt toSource mmod)
    } added
  where
    toSource : (FC, ModuleIdent) -> Core (ModuleIdent, String)
    toSource (loc, ns) = pure (ns, !(nsToSource loc ns))
    go : {auto p : Ref ParsedMods (List (FC, ModuleIdent))} ->
         {auto m : Ref MainMod (Maybe (FC, ModuleIdent))} ->
         List DescField -> PkgDesc -> Core PkgDesc
    go [] dsc = pure dsc
    go (x :: xs) dsc = go xs !(addField x dsc)

runScript : Maybe (FC, String) -> Core ()
runScript Nothing = pure ()
runScript (Just (fc, s))
    = do res <- coreLift $ system s
         when (res /= 0) $
            throw (GenericMsg fc "Script failed")

export
parsePkgFile : {auto c : Ref Ctxt Defs} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto o : Ref ROpts REPLOpts} ->
               (setSrc : Bool) -> -- parse package file as a dependency
               String -> Core PkgDesc
parsePkgFile setSrc file = do
    Right (pname, fs) <- coreLift $ parseFile file $ parsePkgDesc file <* eoi
        | Left err => throw err
    addFields setSrc fs (initPkgDesc pname)

--------------------------------------------------------------------------------
--          Dependency Resolution
--------------------------------------------------------------------------------

record Candidate where
  constructor MkCandidate
  name      : String
  version   : Maybe PkgVersion
  directory : String

toCandidate : (name : String) -> (String,Maybe PkgVersion) -> Candidate
toCandidate name (dir,v) = MkCandidate name v dir

record ResolutionError where
  constructor MkRE
  decisions : List Candidate
  depends   : Depends
  version   : Maybe PkgVersion

prepend : Candidate -> ResolutionError -> ResolutionError
prepend p = { decisions $= (p ::)}

reason : Maybe PkgVersion -> String
reason Nothing  = "no matching version is installed"
reason (Just x) = "assigned version \{show x} which is out of bounds"


printResolutionError : ResolutionError -> String
printResolutionError (MkRE ds d v) = go [<] ds
  where go : SnocList String -> List Candidate -> String
        go ss []        =
          let pre    := "required \{d.pkgname} \{show d.pkgbounds} but"
           in fastConcat . intersperse "; " $ ss <>> ["\{pre} \{reason v}"]
        go ss (c :: cs) =
          let v := fromMaybe defaultVersion c.version
           in go (ss :< "\{c.name}-\{show v}") cs

data ResolutionRes : Type where
  Resolved : List String -> ResolutionRes
  Failed   : List ResolutionError -> ResolutionRes

printErrs : PkgDesc -> List ResolutionError -> String
printErrs x es =
  unlines $  "Failed to resolve the dependencies for \{x.name}:"
          :: map (indent 2 . printResolutionError) es

-- try all possible resolution paths, keeping the first
-- that works
tryAll :  List Candidate
       -> (Candidate -> Core ResolutionRes)
       -> Core ResolutionRes
tryAll ps f = go [<] ps
  where go :  SnocList ResolutionError
           -> List Candidate
           -> Core ResolutionRes
        go se []        = pure (Failed $ se <>> [])
        go se (x :: xs) = do
          Failed errs <- f x | Resolved res => pure (Resolved res)
          go (se <>< map (prepend x) errs) xs

addDeps :
    {auto c : Ref Ctxt Defs} ->
    {auto s : Ref Syn SyntaxInfo} ->
    {auto o : Ref ROpts REPLOpts} ->
    PkgDesc ->
    Core ()
addDeps pkg = do
  Resolved allPkgs <- getTransitiveDeps pkg.depends empty
    | Failed errs => throw $ GenericMsg EmptyFC (printErrs pkg errs)
  log "package.depends" 10 $ "all depends: \{show allPkgs}"
  traverse_ addExtraDir allPkgs
  where
    -- Note: findPkgDir throws an error if a package is not found
    -- *unless* --ignore-missing-ipkg is enabled
    -- therefore, findPkgDir returns Nothing, skip the package
    --
    -- We use a backtracking algorithm here: If several versions of
    -- a package are installed, we must try all, which are are
    -- potentially in bounds, because their set of dependencies
    -- might be different across versions and not all of them
    -- might lead to a resolvable situation.
    getTransitiveDeps :
        List Depends ->
        (done : StringMap (Maybe PkgVersion)) ->
        Core ResolutionRes
    getTransitiveDeps [] done = do
      ms <- for (StringMap.toList done) $
        \(pkg, mv) => findPkgDir pkg (exactBounds mv)
      pure . Resolved $ catMaybes ms

    getTransitiveDeps (dep :: deps) done =
      case lookup dep.pkgname done of
        Just mv =>
          if inBounds mv dep.pkgbounds
            -- already resolved dependency is in bounds
            -- so we keep it and resolve remaining deps
            then getTransitiveDeps deps done
            -- the resolved dependency does not satisfy the
            -- current bounds. we return an error and backtrack
            else pure (Failed [MkRE [] dep $ mv <|> Just defaultVersion])
        Nothing => do
          log "package.depends" 50 "adding new dependency: \{dep.pkgname} (\{show dep.pkgbounds})"
          pkgDirs <- findPkgDirs dep.pkgname dep.pkgbounds
          let candidates := toCandidate dep.pkgname <$> pkgDirs

          case candidates of
            [] => do
              defs <- get Ctxt
              if defs.options.session.ignoreMissingPkg
                -- this corresponds to what `findPkgDir` does in
                -- case of `ignoreMissingPkg` being set to `True`
                then getTransitiveDeps deps done
                else pure (Failed [MkRE [] dep Nothing])

            _  => tryAll candidates $ \(MkCandidate name mv pkgDir) => do
              let pkgFile = pkgDir </> name <.> "ipkg"
              True <- coreLift $ exists pkgFile
                | False => getTransitiveDeps deps (insert name mv done)
              pkg <- parsePkgFile False pkgFile
              getTransitiveDeps
                (pkg.depends ++ deps)
                (insert pkg.name pkg.version done)

--------------------------------------------------------------------------------
--          Processing Options
--------------------------------------------------------------------------------

processOptions : {auto c : Ref Ctxt Defs} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 Maybe (FC, String) -> Core ()
processOptions Nothing = pure ()
processOptions (Just (fc, opts))
    = do let Right clopts = getOpts (words opts)
                | Left err => throw (GenericMsg fc err)
         ignore $ preOptions clopts

compileMain : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
              Name -> String -> String -> Core ()
compileMain mainn mfilename exec
    = do modIdent <- ctxtPathToNS mfilename
         m <- newRef MD (initMetadata (PhysicalIdrSrc modIdent))
         u <- newRef UST initUState
         ignore $ loadMainFile mfilename
         ignore $ compileExp (PRef replFC mainn) exec

prepareCompilation : {auto c : Ref Ctxt Defs} ->
                     {auto s : Ref Syn SyntaxInfo} ->
                     {auto o : Ref ROpts REPLOpts} ->
                     PkgDesc ->
                     List CLOpt ->
                     Core (List Error)
prepareCompilation pkg opts =
  do
    processOptions (options pkg)
    addDeps pkg

    ignore $ preOptions opts

    runScript (prebuild pkg)

    let toBuild = maybe (map snd (modules pkg))
                        (\m => snd m :: map snd (modules pkg))
                        (mainmod pkg)
    buildAll toBuild

assertIdrisCompatibility : PkgDesc -> Core ()
assertIdrisCompatibility pkg
    = do let Just requiredBounds = pkg.langversion
           | Nothing => pure ()
         unless (inBounds version requiredBounds) $
           throw (GenericMsg emptyFC "\{pkg.name} requires Idris2 \{show requiredBounds} but the installed version of Idris2 is \{show Version.version}.")

build : {auto c : Ref Ctxt Defs} ->
        {auto s : Ref Syn SyntaxInfo} ->
        {auto o : Ref ROpts REPLOpts} ->
        PkgDesc ->
        List CLOpt ->
        Core (List Error)
build pkg opts
    = do assertIdrisCompatibility pkg
         [] <- prepareCompilation pkg opts
            | errs => pure errs

         case executable pkg of
              Nothing => pure ()
              Just exec =>
                   do let Just (mainNS, mainFile) = mainmod pkg
                               | Nothing => throw (GenericMsg emptyFC "No main module given")
                      let mainName = NS (miAsNamespace mainNS) (UN $ Basic "main")
                      compileMain mainName mainFile exec

         runScript (postbuild pkg)
         pure []

installFrom : {auto o : Ref ROpts REPLOpts} ->
              {auto c : Ref Ctxt Defs} ->
              String -> String -> ModuleIdent -> Core ()
installFrom builddir destdir ns
    = do let ttcfile = ModuleIdent.toPath ns
         let ttcPath = builddir </> "ttc" </> ttcfile <.> "ttc"
         objPaths_in <- traverse
                     (\cg =>
                        do Just cgdata <- getCG cg
                                | Nothing => pure Nothing
                           let Just ext = incExt cgdata
                                | Nothing => pure Nothing
                           let srcFile = builddir </> "ttc" </> ttcfile <.> ext
                           let destFile = destdir </> ttcfile <.> ext
                           let Just (dir, _) = splitParent destFile
                                | Nothing => pure Nothing
                           ensureDirectoryExists dir
                           pure $ Just (srcFile, destFile))
                     (incrementalCGs !getSession)
         let objPaths = mapMaybe id objPaths_in

         let modPath  = reverse $ fromMaybe [] $ tail' $ unsafeUnfoldModuleIdent ns
         let destNest = joinPath modPath
         let destPath = destdir </> destNest
         let destFile = destdir </> ttcfile <.> "ttc"

         Right _ <- coreLift $ mkdirAll $ destNest
             | Left err => throw $ InternalError $ unlines
                             [ "Can't make directories " ++ show modPath
                             , show err ]
         coreLift $ putStrLn $ "Installing " ++ ttcPath ++ " to " ++ destPath
         Right _ <- coreLift $ copyFile ttcPath destFile
             | Left err => throw $ InternalError $ unlines
                             [ "Can't copy file " ++ ttcPath ++ " to " ++ destPath
                             , show err ]
         -- Copy object files, if any. They don't necessarily get created,
         -- since some modules don't generate any code themselves.
         traverse_ (\ (obj, dest) =>
                      do coreLift $ putStrLn $ "Installing " ++ obj ++ " to " ++ destPath
                         ignore $ coreLift $ copyFile obj dest)
                   objPaths

         pure ()

installSrcFrom : {auto c : Ref Ctxt Defs} ->
                 String -> String -> (ModuleIdent, FileName) -> Core ()
installSrcFrom wdir destdir (ns, srcRelPath)
    = do let srcfile = ModuleIdent.toPath ns
         let srcPath = wdir </> srcRelPath
         let Just ext = extension srcPath
           | _ => throw (InternalError $
                "Unexpected failure when installing source file:\n"
              ++ srcPath
              ++ "\n"
              ++ "Can't extract file extension.")

         let modPath  = reverse $ fromMaybe [] $ tail' $ unsafeUnfoldModuleIdent ns
         let destNest = joinPath modPath
         let destPath = destdir </> destNest
         let destFile = destdir </> srcfile <.> ext

         Right _ <- coreLift $ mkdirAll $ destNest
             | Left err => throw $ InternalError $ unlines
                             [ "Can't make directories " ++ show modPath
                             , show err ]
         coreLift $ putStrLn $ "Installing " ++ srcPath ++ " to " ++ destPath
         when !(coreLift $ exists destFile) $ do
           -- Grant read/write access to the file we are about to overwrite.
           Right _ <- coreLift $ chmod destFile
             (MkPermissions [Read, Write] [Read, Write] [Read, Write])
             | Left err => throw $ UserError (show err)
           pure ()
         Right _ <- coreLift $ copyFile srcPath destFile
             | Left err => throw $ InternalError $ unlines
                             [ "Can't copy file " ++ srcPath ++ " to " ++ destPath
                             , show err ]
         -- Make the source read-only
         Right _ <- coreLift $ chmod destFile (MkPermissions [Read] [Read] [Read])
           | Left err => throw $ UserError (show err)
         pure ()

-- Install all the built modules in prefix/package/
-- We've already built and checked for success, so if any don't exist that's
-- an internal error.
install : {auto c : Ref Ctxt Defs} ->
          {auto o : Ref ROpts REPLOpts} ->
          PkgDesc ->
          List CLOpt ->
          (installSrc : Bool) ->
          Core ()
install pkg opts installSrc -- not used but might be in the future
    = do defs <- get Ctxt
         let build = build_dir (dirs (options defs))
         let src = source_dir (dirs (options defs))
         runScript (preinstall pkg)
         let toInstall = maybe (modules pkg)
                               (:: modules pkg)
                               (mainmod pkg)
         wdir <- getWorkingDir
         -- Make the package installation directory
         let targetDir = prefix_dir (dirs (options defs)) </>
                             "idris2-" ++ showVersion False version </>
                             installDir pkg
         Right _ <- coreLift $ mkdirAll targetDir
             | Left err => throw $ InternalError $ unlines
                             [ "Can't make directory " ++ targetDir
                             , show err ]
         True <- coreLift $ changeDir targetDir
             | False => throw $ InternalError $ "Can't change directory to " ++ targetDir

         -- We're in that directory now, so copy the files from
         -- wdir/build into it
         traverse_ (installFrom (wdir </> build) targetDir . fst) toInstall
         when installSrc $ do
           traverse_ (installSrcFrom wdir targetDir) toInstall

         -- install package file
         let pkgFile = targetDir </> pkg.name <.> "ipkg"
         coreLift $ putStrLn $ "Installing package file for \{pkg.name} to \{targetDir}"
         let pkgStr = String.renderString $ layoutUnbounded $ pretty $ savePkgMetadata pkg
         log "package.depends" 25 $ "  package file:\n\{pkgStr}"
         coreLift_ $ writeFile pkgFile pkgStr

         coreLift_ $ changeDir wdir

         runScript (postinstall pkg)
  where
    savePkgMetadata : PkgDesc -> PkgDesc
    savePkgMetadata pkg =
      the (PkgDesc -> PkgDesc)
      { depends := pkg.depends
      , version := pkg.version
      } $ initPkgDesc pkg.name

-- Check package without compiling anything.
check : {auto c : Ref Ctxt Defs} ->
        {auto s : Ref Syn SyntaxInfo} ->
        {auto o : Ref ROpts REPLOpts} ->
        PkgDesc ->
        List CLOpt ->
        Core (List Error)
check pkg opts =
  do assertIdrisCompatibility pkg
     [] <- prepareCompilation pkg opts
       | errs => pure errs

     runScript (postbuild pkg)
     pure []

makeDoc : {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto o : Ref ROpts REPLOpts} ->
          PkgDesc ->
          List CLOpt ->
          Core (List Error)
makeDoc pkg opts =
    do [] <- prepareCompilation pkg opts
         | errs => pure errs

       defs <- get Ctxt
       let build = build_dir (dirs (options defs))
       let docBase = build </> "docs"
       let docDir = docBase </> "docs"
       Right () <- coreLift $ mkdirAll docDir
         | Left err => fileError docDir err
       u <- newRef UST initUState
       setPPrint (MkPPOpts False True False False)

       [] <- concat <$> for (modules pkg) (\(mod, filename) => do
           -- load dependencies
           let ns = miAsNamespace mod
           addImport (MkImport emptyFC False mod ns)

           -- generate docs for all visible names
           defs <- get Ctxt
           let ctxt = gamma defs
           visibleDefs <- map catMaybes $ for [1..nextEntry ctxt - 1] $ \ i =>
             do -- Select the entries that are from `mod` and visible
                Just gdef <- lookupCtxtExact (Resolved i) ctxt
                  | _ => pure Nothing
                let Just nfc = isNonEmptyFC $ location gdef
                  | _ => do log "doc.module.definitions" 70 $ unwords
                              [ show mod ++ ":"
                              , show (fullname gdef)
                              , "has an empty FC"
                              ]
                            pure Nothing
                let PhysicalIdrSrc mod' = origin nfc
                  | _ => pure Nothing
                let True = mod == mod'
                  | _ => do log "doc.module.definitions" 60 $ unwords
                              [ show mod ++ ":"
                              , show (fullname gdef)
                              , "was defined in"
                              , show mod'
                              ]
                            pure Nothing
                let True = visible gdef
                  | _ => pure Nothing
                pure (Just gdef)

           let outputFilePath = docDir </> (show mod ++ ".html")
           allDocs <- for (sortBy (compare `on` startPos . toNonEmptyFC . location) visibleDefs) $ \ def =>
                        getDocsForName emptyFC (fullname def) shortNamesConfig
           let allDecls = annotate Declarations $ vcat allDocs

           -- grab module header doc
           syn  <- get Syn
           let modDoc = lookup mod (modDocstrings syn)
           log "doc.module" 10 $ unwords
             [ "Looked up doc for"
             , show mod
             , "and got:"
             , show modDoc
             ]
           log "doc.module" 100 $ "from: " ++ show (modDocstrings syn)

           -- grab publically re-exported modules
           let mreexports = do docs <- lookup mod $ modDocexports syn
                               guard (not $ null docs)
                               pure docs
           whenJust mreexports $ \ reexports =>
             log "doc.module" 15 $ unwords
               [ "All imported:", show reexports]

           let modExports = map (map (reAnnotate Syntax . prettyImport)) mreexports

           Right () <- do doc <- renderModuleDoc mod modDoc modExports
                                   (allDecls <$ guard (not $ null allDocs))
                          coreLift $ writeFile outputFilePath doc
             | Left err => fileError (docBase </> "index.html") err

           pure $ the (List Error) []
         )
         | errs => pure errs

       Right () <- coreLift $ writeFile (docBase </> "index.html") $ renderDocIndex pkg
         | Left err => fileError (docBase </> "index.html") err

       errs <- for cssFiles $ \ cssFile => do
          let fn = cssFile.filename ++ ".css"
          css <- readDataFile ("docs/" ++ fn)
          Right () <- coreLift $ writeFile (docBase </> fn) css
            | Left err => fileError (docBase </> fn) err
          pure (the (List Error) [])

       let [] = concat errs
           | err => pure err

       runScript (postbuild pkg)
       pure []
  where
    visible : GlobalDef -> Bool
    visible def = case definition def of
      (DCon _ _ _) => False
      _ => (visibility def /= Private)

    fileError : String -> FileError -> Core (List Error)
    fileError filename err = pure [FileErr filename err]

-- Data.These.bitraverse hand specialised for Core
bitraverseC : (a -> Core c) -> (b -> Core d) -> These a b -> Core (These c d)
bitraverseC f g (This a)   = [| This (f a) |]
bitraverseC f g (That b)   = [| That (g b) |]
bitraverseC f g (Both a b) = [| Both (f a) (g b) |]

-- Data.StringTrie.foldWithKeysM hand specialised for Core
foldWithKeysC : Monoid b => (List String -> Core b) -> (List String -> a -> Core b) -> StringTrie a -> Core b
foldWithKeysC {a} {b} fk fv = go []
  where
  go : List String -> StringTrie a -> Core b
  go ks (MkStringTrie nd) =
    map bifold $ bitraverseC
                   (fv ks)
                   (\sm => foldlC
                             (\x, (k, vs) =>
                               do let ks' = ks++[k]
                                  y <- assert_total $ go ks' vs
                                  z <- fk ks'
                                  pure $ x <+> y <+> z)
                             neutral
                             (StringMap.toList sm))
                   nd

clean : {auto c : Ref Ctxt Defs} ->
        {auto o : Ref ROpts REPLOpts} ->
        PkgDesc ->
        List CLOpt ->
        Core ()
clean pkg opts -- `opts` is not used but might be in the future
    = do defs <- get Ctxt
         runScript (preclean pkg)
         let pkgmods = maybe
                         (map fst (modules pkg))
                         (\m => fst m :: map fst (modules pkg))
                         (mainmod pkg)
         let toClean : List (List String, String)
               = mapMaybe (\ mod => case unsafeUnfoldModuleIdent mod of
                                       [] => Nothing
                                       (x :: xs) => Just(xs, x))
                          pkgmods
         srcdir <- getWorkingDir
         let d = dirs (options defs)
         let builddir = srcdir </> build_dir d </> "ttc"
         let outputdir = srcdir </> outputDirWithDefault d
         -- the usual pair syntax breaks with `No such variable a` here for some reason
         let pkgTrie : StringTrie (List String)
                     = foldl (\trie, ksv =>
                                let ks = Builtin.fst ksv
                                    v = Builtin.snd ksv
                                  in
                                insertWith (reverse ks) (maybe [v] (v::)) trie) empty toClean
         foldWithKeysC (deleteFolder builddir)
                       (\ks => map concat . traverse (deleteBin builddir ks))
                       pkgTrie
         deleteFolder builddir []
         maybe (pure ()) (\e => delete (outputdir </> e))
               (executable pkg)
         runScript (postclean pkg)
  where
    delete : String -> Core ()
    delete path = do Right () <- coreLift $ removeFile path
                       | Left err => pure ()
                     coreLift $ putStrLn $ "Removed: " ++ path

    deleteFolder : String -> List String -> Core ()
    deleteFolder builddir ns = delete $ builddir </> joinPath ns

    deleteBin : String -> List String -> String -> Core ()
    deleteBin builddir ns mod
        = do let ttFile = builddir </> joinPath ns </> mod
             delete $ ttFile <.> "ttc"
             delete $ ttFile <.> "ttm"

-- Just load the given module, if it exists, which will involve building
-- it if necessary
runRepl : {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto o : Ref ROpts REPLOpts} ->
          Maybe String ->
          Core ()
runRepl fname = do
  u <- newRef UST initUState
  origin <- maybe
    (pure $ Virtual Interactive) (\fname => do
      modIdent <- ctxtPathToNS fname
      pure (PhysicalIdrSrc modIdent)
      ) fname
  m <- newRef MD (initMetadata origin)
  case fname of
      Nothing => pure ()
      Just fn => do
        errs <- loadMainFile fn
        displayErrors errs
  repl {u} {s}

||| If the user did not provide a package file we can look in the working
||| directory. If there is exactly one `.ipkg` file then use that!
localPackageFile : Maybe String -> Core String
localPackageFile (Just fp) = pure fp
localPackageFile Nothing
  = do wdir <- getWorkingDir
       tree <- coreLift (explore $ parse wdir)
       let candidates = map fileName tree.files
       case filter (".ipkg" `isSuffixOf`) candidates of
         [fp] => pure fp
         [] => throw $ UserError "No .ipkg file supplied and none could be found in the working directory."
         _ => throw $ UserError "No .ipkg file supplied and the working directory contains more than one."

processPackage : {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 List CLOpt ->
                 (PkgCommand, Maybe String) ->
                 Core ()
processPackage opts (cmd, mfile)
    = withCtxt . withSyn . withROpts $ case cmd of
        Init =>
          do pkg <- coreLift interactive
             let fp = fromMaybe (pkg.name ++ ".ipkg") mfile
             False <- coreLift (exists fp)
               | _ => throw (GenericMsg emptyFC ("File " ++ fp ++ " already exists"))
             Right () <- coreLift $ writeFile fp (show $ pretty pkg)
               | Left err => throw (FileErr fp err)
             pure ()
        _ =>
          do file <- localPackageFile mfile
             let Just (dir, filename) = splitParent file
                 | _ => throw $ InternalError "Tried to split empty string"
             let True = isSuffixOf ".ipkg" filename
                 | _ => do coreLift $ putStrLn ("Packages must have an '.ipkg' extension: " ++ show file ++ ".")
                           coreLift (exitWith (ExitFailure 1))
             setWorkingDir dir
             pkg <- parsePkgFile True filename
             whenJust (builddir pkg) setBuildDir
             setOutputDir (outputdir pkg)
             case cmd of
                  Build => do [] <- build pkg opts
                                 | errs => coreLift (exitWith (ExitFailure 1))
                              pure ()
                  MkDoc => do [] <- makeDoc pkg opts
                                 | errs => coreLift (exitWith (ExitFailure 1))
                              pure ()
                  Install => do [] <- build pkg opts
                                   | errs => coreLift (exitWith (ExitFailure 1))
                                install pkg opts {installSrc = False}
                  InstallWithSrc =>
                             do [] <- build pkg opts
                                   | errs => coreLift (exitWith (ExitFailure 1))
                                install pkg opts {installSrc = True}
                  Typecheck => do
                    [] <- check pkg opts
                      | errs => coreLift (exitWith (ExitFailure 1))
                    pure ()
                  Clean => clean pkg opts
                  REPL => do
                    [] <- build pkg opts
                       | errs => coreLift (exitWith (ExitFailure 1))
                    runRepl (map snd $ mainmod pkg)
                  Init => pure () -- already handled earlier

record PackageOpts where
  constructor MkPFR
  pkgDetails : List (PkgCommand, Maybe String)
  oopts : List CLOpt
  hasError : Bool

partitionOpts : List CLOpt -> PackageOpts
partitionOpts opts = foldr pOptUpdate (MkPFR [] [] False) opts
  where
    data OptType : Type where
      PPackage : PkgCommand -> Maybe String -> OptType
      POpt : OptType
      PIgnore : OptType
      PErr : OptType
    optType : CLOpt -> OptType
    optType (Package cmd f)        = PPackage cmd f
    optType Quiet                  = POpt
    optType Verbose                = POpt
    optType (Timing l)             = POpt
    optType (Logging l)            = POpt
    optType CaseTreeHeuristics     = POpt
    optType (DumpANF f)            = POpt
    optType (DumpCases f)          = POpt
    optType (DumpLifted f)         = POpt
    optType (DumpVMCode f)         = POpt
    optType DebugElabCheck         = POpt
    optType (SetCG f)              = POpt
    optType (IncrementalCG _)      = POpt
    optType (Directive d)          = POpt
    optType (BuildDir f)           = POpt
    optType (OutputDir f)          = POpt
    optType WarningsAsErrors       = POpt
    optType HashesInsteadOfModTime = POpt
    optType Profile                = POpt
    optType (ConsoleWidth n)       = PIgnore
    optType (Color b)              = PIgnore
    optType NoBanner               = PIgnore
    optType x                      = PErr

    pOptUpdate : CLOpt -> (PackageOpts -> PackageOpts)
    pOptUpdate opt with (optType opt)
      pOptUpdate opt | (PPackage cmd f) = {pkgDetails $= ((cmd, f)::)}
      pOptUpdate opt | POpt    = {oopts $= (opt::)}
      pOptUpdate opt | PIgnore = id
      pOptUpdate opt | PErr    = {hasError := True}

errorMsg : String
errorMsg = unlines
  [ "Not all command line options can be used to override package options.\n"
  , "Overridable options are:"
  , "    --quiet"
  , "    --verbose"
  , "    --timing"
  , "    --log <log level>"
  , "    --dumpcases <file>"
  , "    --dumplifted <file>"
  , "    --dumpvmcode <file>"
  , "    --debug-elab-check"
  , "    --codegen <cg>"
  , "    --inc <cg>"
  , "    --directive <directive>"
  , "    --build-dir <dir>"
  , "    --output-dir <dir>"
  ]

export
processPackageOpts : {auto c : Ref Ctxt Defs} ->
                     {auto s : Ref Syn SyntaxInfo} ->
                     {auto o : Ref ROpts REPLOpts} ->
                     List CLOpt -> Core Bool
processPackageOpts opts
    = do (MkPFR cmds@(_::_) opts' err) <- pure $ partitionOpts opts
             | (MkPFR Nil opts' _) => pure False
         if err
           then coreLift $ putStrLn errorMsg
           else traverse_ (processPackage opts') cmds
         pure True


-- find an ipkg file in one of the parent directories
-- If it exists, read it, set the current directory to the root of the source
-- tree, and set the relevant command line options before proceeding
export
findIpkg : {auto c : Ref Ctxt Defs} ->
           {auto r : Ref ROpts REPLOpts} ->
           {auto s : Ref Syn SyntaxInfo} ->
           Maybe String -> Core (Maybe String)
findIpkg fname
   = do Just (dir, ipkgn, up) <- coreLift findIpkgFile
             | Nothing => pure fname
        coreLift_ $ changeDir dir
        setWorkingDir dir
        pkg <- parsePkgFile True ipkgn
        maybe (pure ()) setBuildDir (builddir pkg)
        setOutputDir (outputdir pkg)
        processOptions (options pkg)
        addDeps pkg
        case fname of
             Nothing => pure Nothing
             Just srcpath  =>
                do let src' = up </> srcpath
                   setSource src'
                   update ROpts { mainfile := Just src' }
                   pure (Just src')
  where
    dropHead : String -> List String -> List String
    dropHead str [] = []
    dropHead str (x :: xs)
        = if x == str then xs else x :: xs
