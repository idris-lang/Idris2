module Compiler.Common


import Compiler.ANF
import Compiler.CompileExpr
import Compiler.Inline
import Compiler.LambdaLift
import Compiler.NoMangle
import Compiler.Opts.CSE
import Compiler.VMCode

import Core.Binary.Prims
import Core.Context
import Core.Context.Log
import Core.Directory
import Core.Options
import Core.TT
import Core.TTC
import Libraries.Data.IOArray
import Libraries.Utils.Scheme

import Data.List
import Data.List1
import Libraries.Data.NameMap
import Data.String as String

import Idris.Syntax
import Idris.Env

import System.Directory
import System.Info

%default covering

||| Generic interface to some code generator
public export
record Codegen where
  constructor MkCG
  ||| Compile an Idris 2 expression, saving it to a file.
  compileExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
                (tmpDir : String) -> (outputDir : String) ->
                ClosedTerm -> (outfile : String) -> Core (Maybe String)
  ||| Execute an Idris 2 expression directly.
  executeExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
                (tmpDir : String) -> ClosedTerm -> Core ()
  ||| Incrementally compile definitions in the current module (toIR defs)
  ||| if supported
  ||| Takes a source file name, returns the name of the generated object
  ||| file, if successful, plus any other backend specific data in a list
  ||| of strings. The generated object file should be placed in the same
  ||| directory as the associated TTC.
  incCompileFile : Maybe (Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
                          (sourcefile : String) ->
                          Core (Maybe (String, List String)))
  ||| If incremental compilation is supported, get the output file extension
  incExt : Maybe String

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
      tag Lifted = 1
      tag ANF = 2
      tag VMCode = 3

public export
record CompileData where
  constructor MkCompileData
  mainExpr : CExp [] -- main expression to execute. This also appears in
                     -- the definitions below as MN "__mainExpression" 0
                     -- For incremental compilation and for compiling exported
                     -- names only, this can be set to 'erased'.
  exported : List (Name, String) -- names to be made accessible to the foreign
                     -- and what they should be called in that language
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
          {auto s : Ref Syn SyntaxInfo} ->
          Codegen ->
          ClosedTerm -> (outfile : String) -> Core (Maybe String)
compile {c} {s} cg tm out
    = do d <- getDirs
         let tmpDir = execBuildDir d
         let outputDir = outputDirWithDefault d
         ensureDirectoryExists tmpDir
         ensureDirectoryExists outputDir
         logTime 1 "Code generation overall" $
             compileExpr cg c s tmpDir outputDir tm out

||| execute
||| As with `compile`, produce a functon that executes
||| the `executeExpr` method of the given Codegen
export
execute : {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          Codegen -> ClosedTerm -> Core ()
execute {c} {s} cg tm
    = do d <- getDirs
         let tmpDir = execBuildDir d
         ensureDirectoryExists tmpDir
         executeExpr cg c s tmpDir tm

export
incCompile : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             Codegen -> String -> Core (Maybe (String, List String))
incCompile {c} {s} cg src
    = do let Just inc = incCompileFile cg
             | Nothing => pure Nothing
         inc c s src

-- If an entry isn't already decoded, get the minimal entry we need for
-- compilation, and record the Binary so that we can put it back when we're
-- done (so that we don't obliterate the definition)
getMinimalDef : ContextEntry -> Core (GlobalDef, Maybe (Namespace, Binary))
getMinimalDef (Decoded def) = pure (def, Nothing)
getMinimalDef (Coded ns bin)
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
                           None cdef Nothing [] Nothing
         pure (def, Just (ns, bin))

-- ||| Recursively get all calls in a function definition
-- ||| Note: this only checks resolved names
getAllDesc : {auto c : Ref Ctxt Defs} ->
             List Name -> -- calls to check
             IOArray (Int, Maybe (Namespace, Binary)) ->
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
            Nothing => do log "compile.execute" 20 $ "Couldn't find " ++ show n
                          getAllDesc rest arr defs
            Just (_, entry) =>
              do (def, bin) <- getMinimalDef entry
                 ignore $ addDef n def
                 let refs = refersToRuntime def
                 if multiplicity def /= erased
                    then do coreLift $ writeArray arr i (i, bin)
                            let refs = refersToRuntime def
                            refs' <- traverse toResolvedNames (keys refs)
                            getAllDesc (refs' ++ rest) arr defs
                    else do log "compile.execute" 20
                               $ "Dropping " ++ show n ++ " because it's erased"
                            getAllDesc rest arr defs
getAllDesc (n :: rest) arr defs
  = do log "compile.execute" 20 $
         "Ignoring " ++ show n ++ " because it's not a Resolved name"
       getAllDesc rest arr defs

warnIfHole : Name -> NamedDef -> Core ()
warnIfHole n (MkNmError _)
    = coreLift $ putStrLn $ "Warning: compiling hole " ++ show n
warnIfHole n _ = pure ()

getNamedDef :  {auto c : Ref Ctxt Defs}
            -> (Name,FC,CDef)
            -> Core (Name, FC, NamedDef)
getNamedDef (n,fc,cdef) =
  let ndef = forgetDef cdef
   in warnIfHole n ndef >> pure (n,fc,ndef)

replaceEntry : {auto c : Ref Ctxt Defs} ->
               (Int, Maybe (Namespace, Binary)) -> Core ()
replaceEntry (i, Nothing) = pure ()
replaceEntry (i, Just (ns, b))
    = ignore $ addContextEntry ns (Resolved i) b

natHackNames : List Name
natHackNames
    = [UN (Basic "prim__add_Integer"),
       UN (Basic "prim__sub_Integer"),
       UN (Basic "prim__mul_Integer"),
       NS typesNS (UN $ Basic "prim__integerToNat")]

dumpIR : Show def => String -> List (Name, def) -> Core ()
dumpIR fn lns
    = do let cstrs = map dumpDef lns
         Right () <- coreLift $ writeFile fn (fastConcat cstrs)
               | Left err => throw (FileErr fn err)
         pure ()
  where
    fullShow : Name -> String
    fullShow (DN _ n) = show n
    fullShow n = show n

    dumpDef : (Name, def) -> String
    dumpDef (n, d) = fullShow n ++ " = " ++ show d ++ "\n"


export
nonErased : {auto c : Ref Ctxt Defs} ->
            Name -> Core Bool
nonErased n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure True
         pure (multiplicity gdef /= erased)

-- Get the names of the functions we're exporting to the given back end, and
-- the corresponding name it will have when exported.
getExported : String -> NameMap (List (String, String)) -> List (Name, String)
getExported backend all
    = mapMaybe isExp (toList all)
  where
    -- If the name/convention pair matches the backend, keep the name
    isExp : (Name, List (String, String)) -> Maybe (Name, String)
    isExp (n, cs)
        = do fn <- lookup backend cs
             pure (n, fn)

-- Find all the names which need compiling, from a given expression, and compile
-- them to CExp form (and update that in the Defs).
-- Return the names, the type tags, and a compiled version of the expression
export
getCompileDataWith : {auto c : Ref Ctxt Defs} ->
                     List String -> -- which FFI(s), if compiling foreign exports
                     (doLazyAnnots : Bool) ->
                     UsePhase -> ClosedTerm -> Core CompileData
getCompileDataWith exports doLazyAnnots phase_in tm_in
    = do log "compile.execute" 10 $ "Getting compiled data for: " ++ show tm_in
         sopts <- getSession
         let phase = foldl {t=List} (flip $ maybe id max) phase_in $
                       [ Cases <$ dumpcases sopts
                       , Lifted <$ dumplifted sopts
                       , ANF <$ dumpanf sopts
                       , VMCode <$ dumpvmcode sopts
                       ]

         -- When we compile a REPL expression, there may be leftovers holes in it.
         -- Turn these into runtime errors.
         let metas = addMetas True empty tm_in
         for_ (keys metas) $ \ metanm =>
             do defs <- get Ctxt
                Just gdef <- lookupCtxtExact metanm (gamma defs)
                  | Nothing => log "compile.execute" 50 $ unwords
                                    [ "Couldn't find"
                                    , show metanm
                                    , "(probably impossible)"]
                let Hole _ _ = definition gdef
                  | _ => pure ()
                let fulln = fullname gdef
                let cexp = MkError $ CCrash emptyFC
                         $ "Encountered unimplemented hole " ++ show fulln
                ignore $ addDef metanm ({ compexpr := Just cexp
                                        , namedcompexpr := Just (forgetDef cexp)
                                        } gdef)

         defs <- get Ctxt
         let refs  = getRefs (Resolved (-1)) tm_in
         exported <- if isNil exports
                 then pure []
                 else getExports defs
         log "compile.export" 25 "exporting: \{show $ map fst exported}"
         let ns = keys (mergeWith const metas refs) ++ map fst exported
         log "compile.execute" 70 $
           "Found names: " ++ concat (intersperse ", " $ map show $ ns)
         tm <- toFullNames tm_in
         natHackNames' <- traverse toResolvedNames natHackNames
         -- make an array of Bools to hold which names we've found (quicker
         -- to check than a NameMap!)
         asize <- getNextEntry
         arr <- coreLift $ newArray asize

         defs <- get Ctxt
         logTime 2 "Get names" $ getAllDesc (natHackNames' ++ ns) arr defs

         let entries = catMaybes !(coreLift (toList arr))
         let allNs = map (Resolved . fst) entries
         cns <- traverse toFullNames allNs
         log "compile.execute" 30 $
           "All names: " ++ concat (intersperse ", " $ map show $ zip allNs cns)

         -- Do a round of merging/arity fixing for any names which were
         -- unknown due to cyclic modules (i.e. declared in one, defined in
         -- another)
         rcns <- filterM nonErased cns
         log "compile.execute" 40 $
           "Kept: " ++ concat (intersperse ", " $ map show rcns)

         logTime 2 "Merge lambda" $ traverse_ mergeLamDef rcns
         logTime 2 "Fix arity" $ traverse_ fixArityDef rcns
         compiledtm <- fixArityExp !(compileExp tm)

         (cseDefs, csetm) <- logTime 2 "CSE" $ cse rcns compiledtm

         namedDefs <- logTime 2 "Forget names" $
           traverse getNamedDef cseDefs

         let mainname = MN "__mainExpression" 0
         (liftedtm, ldefs) <- liftBody {doLazyAnnots} mainname csetm

         lifted_in <- if phase >= Lifted
                         then logTime 2 "Lambda lift" $
                              traverse (lambdaLift doLazyAnnots) cseDefs
                         else pure []

         let lifted = (mainname, MkLFun [] [] liftedtm) ::
                      ldefs ++ concat lifted_in

         anf <- if phase >= ANF
                   then logTime 2 "Get ANF" $ traverse (\ (n, d) => pure (n, !(toANF d))) lifted
                   else pure []
         vmcode <- if phase >= VMCode
                      then logTime 2 "Get VM Code" $ pure (allDefs anf)
                      else pure []

         defs <- get Ctxt
         whenJust (dumpcases sopts) $ \ f =>
            do coreLift $ putStrLn $ "Dumping case trees to " ++ f
               dumpIR f (map (\(n, _, def) => (n, def)) namedDefs)

         whenJust (dumplifted sopts) $ \ f =>
            do coreLift $ putStrLn $ "Dumping lambda lifted defs to " ++ f
               dumpIR f lifted

         whenJust (dumpanf sopts) $ \ f =>
            do coreLift $ putStrLn $ "Dumping ANF defs to " ++ f
               dumpIR f anf

         whenJust (dumpvmcode sopts) $ \ f =>
            do coreLift $ putStrLn $ "Dumping VM defs to " ++ f
               dumpIR f vmcode

         -- We're done with our minimal context now, so put it back the way
         -- it was. Back ends shouldn't look at the global context, because
         -- it'll have to decode the definitions again.
         traverse_ replaceEntry entries
         pure (MkCompileData csetm exported namedDefs lifted anf vmcode)
  where
    lookupBackend :
        List String ->
        (Name, List (String, String)) ->
        Maybe (Name, String)
    lookupBackend [] _ = Nothing
    lookupBackend (b :: bs) (n, exps) = case find (\(b', _) => b == b') exps of
        Just (_, exp) => Just (n, exp)
        Nothing => lookupBackend bs (n, exps)

    getExports : Defs -> Core (List (Name, String))
    getExports defs = traverse (\(n, exp) => pure (!(resolved defs.gamma n), exp)) $
        mapMaybe (lookupBackend exports) (toList defs.foreignExports)

-- Find all the names which need compiling, from a given expression, and compile
-- them to CExp form (and update that in the Defs).
-- Return the names, the type tags, and a compiled version of the expression
export
getCompileData : {auto c : Ref Ctxt Defs} ->
                 (doLazyAnnots : Bool) ->
                 UsePhase -> ClosedTerm -> Core CompileData
getCompileData = getCompileDataWith []

export
compileTerm : {auto c : Ref Ctxt Defs} ->
              ClosedTerm -> Core (CExp [])
compileTerm tm_in
    = do tm <- toFullNames tm_in
         fixArityExp !(compileExp tm)

compDef : {auto c : Ref Ctxt Defs} -> Name -> Core (Maybe (Name, FC, CDef))
compDef n = do
  defs <- get Ctxt
  Just def <- lookupCtxtExact n (gamma defs) | Nothing => pure Nothing
  let Just cexpr =  compexpr def             | Nothing => pure Nothing
  pure $ Just (n, location def, cexpr)

export
getIncCompileData : {auto c : Ref Ctxt Defs} ->
                    (doLazyAnnots : Bool) ->
                    UsePhase -> Core CompileData
getIncCompileData doLazyAnnots phase
    = do defs <- get Ctxt
         -- Compile all the names in 'toIR', since those are the ones defined
         -- in the current source file
         let ns = keys (toIR defs)
         cns <- traverse toFullNames ns
         rcns <- filterM nonErased cns
         cseDefs <- catMaybes <$> traverse compDef rcns

         namedDefs <- traverse getNamedDef cseDefs

         lifted_in <- if phase >= Lifted
                         then logTime 2 "Lambda lift" $
                              traverse (lambdaLift doLazyAnnots) cseDefs
                         else pure []
         let lifted = concat lifted_in
         anf <- if phase >= ANF
                   then logTime 2 "Get ANF" $ traverse (\ (n, d) => pure (n, !(toANF d))) lifted
                   else pure []
         vmcode <- if phase >= VMCode
                      then logTime 2 "Get VM Code" $ pure (allDefs anf)
                      else pure []
         pure (MkCompileData (CErased emptyFC) [] namedDefs lifted anf vmcode)

-- Some things missing from Prelude.File


||| check to see if a given file exists
export
exists : String -> IO Bool
exists f
    = do Right ok <- openFile f Read
             | Left err => pure False
         closeFile ok
         pure True
-- Select the most preferred target from an ordered list of choices and
-- parse the calling convention into a backend/target for the call, and
-- a comma separated list of any other location data. For example
-- the chez backend would supply ["scheme,chez", "scheme", "C"]. For a function with
-- more than one string, a string with "scheme" would be preferred over one
-- with "C" and "scheme,chez" would be preferred to both.
-- e.g. "scheme:display" - call the scheme function 'display'
--      "C:puts,libc,stdio.h" - call the C function 'puts' which is in
--      the library libc and the header stdio.h
-- Returns Nothing if there is no match.
export
parseCC : List String -> List String -> Maybe (String, List String)
parseCC [] _ = Nothing
parseCC (target::ts) strs = findTarget target strs <|> parseCC ts strs
  where
    getOpts : String -> List String
    getOpts "" = []
    getOpts str
        = case span (/= ',') str of
               (opt, "") => [opt]
               (opt, rest) => opt :: getOpts (assert_total (strTail rest))
    hasTarget : String -> String -> Bool
    hasTarget target str = case span (/= ':') str of
                            (targetSpec, _) => targetSpec == target
    findTarget : String -> List String -> Maybe (String, List String)
    findTarget target [] = Nothing
    findTarget target (s::xs) = if hasTarget target s
                                  then case span (/= ':') s of
                                        (t, "") => Just (trim t, [])
                                        (t, opts) => Just (trim t, map trim (getOpts
                                                                  (assert_total (strTail opts))))
                                  else findTarget target xs

export
dylib_suffix : String
dylib_suffix
    = cond [(elem os $ the (List String) ["windows", "mingw32", "cygwin32"], "dll"),
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

||| Cast implementations. Values of `ConstantPrimitives` can
||| be used in a call to `castInt`, which then determines
||| the cast implementation based on the given pair of
||| constants.
public export
record ConstantPrimitives where
  constructor MkConstantPrimitives
  charToInt    : IntKind -> String -> Core String
  intToChar    : IntKind -> String -> Core String
  stringToInt  : IntKind -> String -> Core String
  intToString  : IntKind -> String -> Core String
  doubleToInt  : IntKind -> String -> Core String
  intToDouble  : IntKind -> String -> Core String
  intToInt     : IntKind -> IntKind -> String -> Core String

||| Implements casts from and to integral types by using
||| the implementations from the provided `ConstantPrimitives`.
export
castInt :  ConstantPrimitives
        -> PrimType
        -> PrimType
        -> String
        -> Core String
castInt p from to x =
  case ((from, intKind from), (to, intKind to)) of
       ((CharType, _)  , (_, Just k)) => p.charToInt k x
       ((StringType, _), (_, Just k)) => p.stringToInt k x
       ((DoubleType, _), (_, Just k)) => p.doubleToInt k x
       ((_, Just k), (CharType, _))   => p.intToChar k x
       ((_, Just k), (StringType, _)) => p.intToString k x
       ((_, Just k), (DoubleType, _)) => p.intToDouble k x
       ((_, Just k1), (_, Just k2))   => p.intToInt k1 k2 x
       _ => throw $ InternalError $ "invalid cast: + " ++ show from ++ " + ' -> ' + " ++ show to
