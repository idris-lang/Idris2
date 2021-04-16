module Compiler.Common


import Compiler.ANF
import Compiler.CompileExpr
import Compiler.Inline
import Compiler.LambdaLift
import Compiler.VMCode

import Core.Context
import Core.Context.Log
import Core.Directory
import Core.Options
import Core.TT
import Core.TTC
import Libraries.Utils.Binary
import Libraries.Utils.Path

import Data.IOArray
import Data.List
import Data.List1
import Libraries.Data.NameMap
import Data.Strings as String

import Idris.Env

import System.Directory
import System.Info
import System.File

%default covering

||| Generic interface to some code generator
public export
record Codegen where
  constructor MkCG
  ||| Compile an Idris 2 expression, saving it to a file.
  compileExpr : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
                ClosedTerm -> (outfile : String) -> Core (Maybe String)
  ||| Execute an Idris 2 expression directly.
  executeExpr : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()

-- Say which phase of compilation is the last one to use - it saves time if
-- you only ask for what you need.
public export
data UsePhase = Cases | Lifted | ANF | VMCode

Eq UsePhase where
  (==) Cases Cases = True
  (==) Lifted Lifted = True
  (==) ANF ANF = True
  (==) VMCode VMCode = True
  (==) _ _ = False

Ord UsePhase where
  compare x y = compare (tag x) (tag y)
    where
      tag : UsePhase -> Int
      tag Cases = 0
      tag Lifted = 0
      tag ANF = 0
      tag VMCode = 0

public export
record CompileData where
  constructor MkCompileData
  mainExpr : CExp [] -- main expression to execute. This also appears in
                     -- the definitions below as MN "__mainExpression" 0
  namedDefs : List (Name, FC, NamedDef)
  lambdaLifted : List (Name, LiftedDef)
       -- ^ lambda lifted definitions, if required. Only the top level names
       -- will be in the context, and (for the moment...) I don't expect to
       -- need to look anything up, so it's just an alist.
  anf : List (Name, ANFDef)
       -- ^ lambda lifted and converted to ANF (all arguments to functions
       -- and constructors transformed to either variables or Null if erased)
  vmcode : List (Name, VMDef)
       -- ^ A much simplified virtual machine code, suitable for passing
       -- to a more low level target such as C

||| compile
||| Given a value of type Codegen, produce a standalone function
||| that executes the `compileExpr` method of the Codegen
export
compile : {auto c : Ref Ctxt Defs} ->
          Codegen ->
          ClosedTerm -> (outfile : String) -> Core (Maybe String)
compile {c} cg tm out
    = do d <- getDirs
         let tmpDir = execBuildDir d
         let outputDir = outputDirWithDefault d
         ensureDirectoryExists tmpDir
         ensureDirectoryExists outputDir
         logTime "+ Code generation overall" $
             compileExpr cg c tmpDir outputDir tm out

||| execute
||| As with `compile`, produce a functon that executes
||| the `executeExpr` method of the given Codegen
export
execute : {auto c : Ref Ctxt Defs} ->
          Codegen -> ClosedTerm -> Core ()
execute {c} cg tm
    = do d <- getDirs
         let tmpDir = execBuildDir d
         ensureDirectoryExists tmpDir
         executeExpr cg c tmpDir tm
         pure ()

-- If an entry isn't already decoded, get the minimal entry we need for
-- compilation, and record the Binary so that we can put it back when we're
-- done (so that we don't obliterate the definition)
getMinimalDef : ContextEntry -> Core (GlobalDef, Maybe Binary)
getMinimalDef (Decoded def) = pure (def, Nothing)
getMinimalDef (Coded bin)
    = do b <- newRef Bin bin
         cdef <- fromBuf b
         refsRList <- fromBuf b
         let refsR = map fromList refsRList
         fc <- fromBuf b
         mul <- fromBuf b
         name <- fromBuf b
         let def
             = MkGlobalDef fc name (Erased fc False) [] [] [] [] mul
                           [] Public (MkTotality Unchecked IsCovering)
                           [] Nothing refsR False False True
                           None cdef Nothing []
         pure (def, Just bin)

-- ||| Recursively get all calls in a function definition
getAllDesc : {auto c : Ref Ctxt Defs} ->
             List Name -> -- calls to check
             IOArray (Int, Maybe Binary) ->
                            -- which nodes have been visited. If the entry is
                            -- present, it's visited. Keep the binary entry, if
                            -- we partially decoded it, so that we can put back
                            -- the full definition later.
                            -- (We only need to decode the case tree IR, and
                            -- it's expensive to decode the whole thing)
             Defs -> Core ()
getAllDesc [] arr defs = pure ()
getAllDesc (n@(Resolved i) :: rest) arr defs
  = do Nothing <- coreLift $ readArray arr i
           | Just _ => getAllDesc rest arr defs
       case !(lookupContextEntry n (gamma defs)) of
            Nothing => getAllDesc rest arr defs
            Just (_, entry) =>
              do (def, bin) <- getMinimalDef entry
                 ignore $ addDef n def
                 let refs = refersToRuntime def
                 if multiplicity def /= erased
                    then do coreLift $ writeArray arr i (i, bin)
                            let refs = refersToRuntime def
                            refs' <- traverse toResolvedNames (keys refs)
                            getAllDesc (refs' ++ rest) arr defs
                    else getAllDesc rest arr defs
getAllDesc (n :: rest) arr defs
  = getAllDesc rest arr defs

warnIfHole : Name -> NamedDef -> Core ()
warnIfHole n (MkNmError _)
    = coreLift $ putStrLn $ "Warning: compiling hole " ++ show n
warnIfHole n _ = pure ()

getNamedDef : {auto c : Ref Ctxt Defs} ->
              Name -> Core (Maybe (Name, FC, NamedDef))
getNamedDef n
    = do defs <- get Ctxt
         case !(lookupCtxtExact n (gamma defs)) of
              Nothing => pure Nothing
              Just def => case namedcompexpr def of
                               Nothing => pure Nothing
                               Just d => do warnIfHole n d
                                            pure (Just (n, location def, d))

replaceEntry : {auto c : Ref Ctxt Defs} ->
               (Int, Maybe Binary) -> Core ()
replaceEntry (i, Nothing) = pure ()
replaceEntry (i, Just b)
    = ignore $ addContextEntry (Resolved i) b

natHackNames : List Name
natHackNames
    = [UN "prim__add_Integer",
       UN "prim__sub_Integer",
       UN "prim__mul_Integer",
       NS typesNS (UN "prim__integerToNat")]

-- Hmm, these dump functions are all very similar aren't they...
dumpCases : Defs -> String -> List Name ->
            Core ()
dumpCases defs fn cns
    = do cstrs <- traverse dumpCase cns
         Right () <- coreLift $ writeFile fn (fastAppend cstrs)
               | Left err => throw (FileErr fn err)
         pure ()
  where
    fullShow : Name -> String
    fullShow (DN _ n) = show n
    fullShow n = show n

    dumpCase : Name -> Core String
    dumpCase n
        = case !(lookupCtxtExact n (gamma defs)) of
               Nothing => pure ""
               Just d =>
                    case namedcompexpr d of
                         Nothing => pure ""
                         Just def => pure (fullShow n ++ " = " ++ show def ++ "\n")

dumpLifted : String -> List (Name, LiftedDef) -> Core ()
dumpLifted fn lns
    = do let cstrs = map dumpDef lns
         Right () <- coreLift $ writeFile fn (fastAppend cstrs)
               | Left err => throw (FileErr fn err)
         pure ()
  where
    fullShow : Name -> String
    fullShow (DN _ n) = show n
    fullShow n = show n

    dumpDef : (Name, LiftedDef) -> String
    dumpDef (n, d) = fullShow n ++ " = " ++ show d ++ "\n"

dumpANF : String -> List (Name, ANFDef) -> Core ()
dumpANF fn lns
    = do let cstrs = map dumpDef lns
         Right () <- coreLift $ writeFile fn (fastAppend cstrs)
               | Left err => throw (FileErr fn err)
         pure ()
  where
    fullShow : Name -> String
    fullShow (DN _ n) = show n
    fullShow n = show n

    dumpDef : (Name, ANFDef) -> String
    dumpDef (n, d) = fullShow n ++ " = " ++ show d ++ "\n"

dumpVMCode : String -> List (Name, VMDef) -> Core ()
dumpVMCode fn lns
    = do let cstrs = map dumpDef lns
         Right () <- coreLift $ writeFile fn (fastAppend cstrs)
               | Left err => throw (FileErr fn err)
         pure ()
  where
    fullShow : Name -> String
    fullShow (DN _ n) = show n
    fullShow n = show n

    dumpDef : (Name, VMDef) -> String
    dumpDef (n, d) = fullShow n ++ " = " ++ show d ++ "\n"

-- Find all the names which need compiling, from a given expression, and compile
-- them to CExp form (and update that in the Defs).
-- Return the names, the type tags, and a compiled version of the expression
export
getCompileData : {auto c : Ref Ctxt Defs} -> (doLazyAnnots : Bool) ->
                 UsePhase -> ClosedTerm -> Core CompileData
getCompileData doLazyAnnots phase tm_in
    = do defs <- get Ctxt
         sopts <- getSession
         let ns = getRefs (Resolved (-1)) tm_in
         tm <- toFullNames tm_in
         natHackNames' <- traverse toResolvedNames natHackNames
         -- make an array of Bools to hold which names we've found (quicker
         -- to check than a NameMap!)
         asize <- getNextEntry
         arr <- coreLift $ newArray asize
         logTime "++ Get names" $ getAllDesc (natHackNames' ++ keys ns) arr defs

         let entries = mapMaybe id !(coreLift (toList arr))
         let allNs = map (Resolved . fst) entries
         cns <- traverse toFullNames allNs

         -- Do a round of merging/arity fixing for any names which were
         -- unknown due to cyclic modules (i.e. declared in one, defined in
         -- another)
         rcns <- filterM nonErased cns
         logTime "++ Merge lambda" $ traverse_ mergeLamDef rcns
         logTime "++ Fix arity" $ traverse_ fixArityDef rcns
         logTime "++ Forget names" $ traverse_ mkForgetDef rcns

         compiledtm <- fixArityExp !(compileExp tm)
         let mainname = MN "__mainExpression" 0
         (liftedtm, ldefs) <- liftBody {doLazyAnnots} mainname compiledtm

         namedefs <- traverse getNamedDef rcns
         lifted_in <- if phase >= Lifted
                         then logTime "++ Lambda lift" $ traverse (lambdaLift doLazyAnnots) rcns
                         else pure []

         let lifted = (mainname, MkLFun [] [] liftedtm) ::
                      ldefs ++ concat lifted_in

         anf <- if phase >= ANF
                   then logTime "++ Get ANF" $ traverse (\ (n, d) => pure (n, !(toANF d))) lifted
                   else pure []
         vmcode <- if phase >= VMCode
                      then logTime "++ Get VM Code" $ pure (allDefs anf)
                      else pure []

         defs <- get Ctxt
         maybe (pure ())
               (\f => do coreLift $ putStrLn $ "Dumping case trees to " ++ f
                         dumpCases defs f rcns)
               (dumpcases sopts)
         maybe (pure ())
               (\f => do coreLift $ putStrLn $ "Dumping lambda lifted defs to " ++ f
                         dumpLifted f lifted)
               (dumplifted sopts)
         maybe (pure ())
               (\f => do coreLift $ putStrLn $ "Dumping ANF defs to " ++ f
                         dumpANF f anf)
               (dumpanf sopts)
         maybe (pure ())
               (\f => do coreLift $ putStrLn $ "Dumping VM defs to " ++ f
                         dumpVMCode f vmcode)
               (dumpvmcode sopts)

         -- We're done with our minimal context now, so put it back the way
         -- it was. Back ends shouldn't look at the global context, because
         -- it'll have to decode the definitions again.
         traverse_ replaceEntry entries
         pure (MkCompileData compiledtm
                             (mapMaybe id namedefs)
                             lifted anf vmcode)
  where
    nonErased : Name -> Core Bool
    nonErased n
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure True
             pure (multiplicity gdef /= erased)

-- Some things missing from Prelude.File

||| check to see if a given file exists
export
exists : String -> IO Bool
exists f
    = do Right ok <- openFile f Read
             | Left err => pure False
         closeFile ok
         pure True

-- Parse a calling convention into a backend/target for the call, and
-- a comma separated list of any other location data.
-- e.g. "scheme:display" - call the scheme function 'display'
--      "C:puts,libc,stdio.h" - call the C function 'puts' which is in
--      the library libc and the header stdio.h
-- Returns Nothing if the string is empty (which a backend can interpret
-- however it likes)
export
parseCC : String -> Maybe (String, List String)
parseCC "" = Nothing
parseCC str
    = case span (/= ':') str of
           (target, "") => Just (trim target, [])
           (target, opts) => Just (trim target,
                                   map trim (getOpts
                                       (assert_total (strTail opts))))
  where
    getOpts : String -> List String
    getOpts "" = []
    getOpts str
        = case span (/= ',') str of
               (opt, "") => [opt]
               (opt, rest) => opt :: getOpts (assert_total (strTail rest))

export
dylib_suffix : String
dylib_suffix
    = cond [(os `elem` ["windows", "mingw32", "cygwin32"], "dll"),
            (os == "darwin", "dylib")]
           "so"

export
locate : {auto c : Ref Ctxt Defs} ->
         String -> Core (String, String)
locate libspec
    = do -- Attempt to turn libspec into an appropriate filename for the system
         let fname
              = case words libspec of
                     [] => ""
                     [fn] => if '.' `elem` unpack fn
                                then fn -- full filename given
                                else -- add system extension
                                     fn ++ "." ++ dylib_suffix
                     (fn :: ver :: _) =>
                          -- library and version given, build path name as
                          -- appropriate for the system
                          cond [(dylib_suffix == "dll",
                                      fn ++ "-" ++ ver ++ ".dll"),
                                (dylib_suffix == "dylib",
                                      fn ++ "." ++ ver ++ ".dylib")]
                                (fn ++ "." ++ dylib_suffix ++ "." ++ ver)

         fullname <- catch (findLibraryFile fname)
                           (\err => -- assume a system library so not
                                    -- in our library path
                                    pure fname)
         pure (fname, fullname)

export
copyLib : (String, String) -> Core ()
copyLib (lib, fullname)
    = if lib == fullname
         then pure ()
         else do Right bin <- coreLift $ readFromFile fullname
                    | Left err => pure () -- assume a system library installed globally
                 Right _ <- coreLift $ writeToFile lib bin
                    | Left err => throw (FileErr lib err)
                 pure ()


-- parses `--directive extraRuntime=/path/to/defs.scm` options for textual inclusion in generated
-- source. Use with `%foreign "scheme:..."` declarations to write runtime-specific scheme calls.
export
getExtraRuntime : List String -> Core String
getExtraRuntime directives
    = do fileContents <- traverse readPath paths
         pure $ concat $ intersperse "\n" fileContents
  where
    getArg : String -> Maybe String
    getArg directive =
      let (k,v) = break (== '=') directive
      in
        if (trim k) == "extraRuntime"
          then Just $ trim $ substr 1 (length v) v
          else Nothing

    paths : List String
    paths = nub $ mapMaybe getArg $ reverse directives

    readPath : String -> Core String
    readPath p = do
      Right contents <- coreLift $ readFile p
        | Left err => throw (FileErr p err)
      pure contents

||| Looks up an executable from a list of candidate names in the PATH
export
pathLookup : List String -> IO (Maybe String)
pathLookup candidates
    = do path <- idrisGetEnv "PATH"
         let extensions = if isWindows then [".exe", ".cmd", ".bat", ""] else [""]
         let pathList = forget $ String.split (== pathSeparator) $ fromMaybe "/usr/bin:/usr/local/bin" path
         let candidates = [p ++ "/" ++ x ++ y | p <- pathList,
                                                x <- candidates,
                                                y <- extensions ]
         firstExists candidates
