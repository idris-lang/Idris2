||| Reading and writing 'Defs' from/to a binary file. In order to be saved, a
||| name must have been flagged using 'toSave'. (Otherwise we'd save out
||| everything, not just the things in the current file).
module Core.Binary

import public Core.Binary.Prims
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Name.Namespace
import Core.Options
import Core.TT
import Core.TTC
import Core.UnifyState

import Data.List
import Data.String

import System.File

import Libraries.Data.NameMap

import public Libraries.Utils.Binary

%default covering

||| TTC files can only be compatible if the version number is the same
||| Update with the current date in YYYYMMDD format, or bump the auxiliary
||| version number if you're changing the version more than once in the same day.
export
ttcVersion : Int
ttcVersion = 20220425 * 100 + 0

export
checkTTCVersion : String -> Int -> Int -> Core ()
checkTTCVersion file ver exp
  = when (ver /= exp) (throw $ TTCError $ Format file ver exp)

record TTCFile extra where
  constructor MkTTCFile
  version : Int
  totalReq : TotalReq
  sourceHash : Maybe String
  ifaceHash : Int
  importHashes : List (Namespace, Int)
  incData : List (CG, String, List String)
  context : List (Name, Binary)
  userHoles : List Name
  autoHints : List (Name, Bool)
  typeHints : List (Name, Name, Bool)
  imported : List (ModuleIdent, Bool, Namespace)
  nextVar : Int
  currentNS : Namespace
  nestedNS : List Namespace
  pairnames : Maybe PairNames
  rewritenames : Maybe RewriteNames
  primnames : PrimNames
  namedirectives : List (Name, List String)
  cgdirectives : List (CG, String)
  transforms : List (Name, Transform)
  foreignExports : List (Name, (List (String, String)))
  extraData : extra

HasNames a => HasNames (List a) where
  full c ns = full_aux c [] ns
    where full_aux : Context -> List a -> List a -> Core (List a)
          full_aux c res [] = pure (reverse res)
          full_aux c res (n :: ns) = full_aux c (!(full c n):: res) ns


  resolved c ns = resolved_aux c [] ns
    where resolved_aux : Context -> List a -> List a -> Core (List a)
          resolved_aux c res [] = pure (reverse res)
          resolved_aux c res (n :: ns) = resolved_aux c (!(resolved c n) :: res) ns
HasNames (Int, FC, Name) where
  full c (i, fc, n) = pure (i, fc, !(full c n))
  resolved c (i, fc, n) = pure (i, fc, !(resolved c n))

HasNames (Name, Bool) where
  full c (n, b) = pure (!(full c n), b)
  resolved c (n, b) = pure (!(resolved c n), b)

HasNames (Name, List a) where
  full c (n, b) = pure (!(full c n), b)
  resolved c (n, b) = pure (!(resolved c n), b)

HasNames (Name, Transform) where
  full c (n, b) = pure (!(full c n), !(full c b))
  resolved c (n, b) = pure (!(resolved c n), !(resolved c b))

HasNames (Name, Name, Bool) where
  full c (n1, n2, b) = pure (!(full c n1), !(full c n2), b)
  resolved c (n1, n2, b) = pure (!(resolved c n1), !(resolved c n2), b)

HasNames e => HasNames (TTCFile e) where
  full gam (MkTTCFile version totalReq sourceHash ifaceHash iHashes incData
                      context userHoles
                      autoHints typeHints
                      imported nextVar currentNS nestedNS
                      pairnames rewritenames primnames
                      namedirectives cgdirectives trans
                      fexp extra)
      = pure $ MkTTCFile version totalReq sourceHash ifaceHash iHashes incData
                         context userHoles
                         !(traverse (full gam) autoHints)
                         !(traverse (full gam) typeHints)
                         imported nextVar currentNS nestedNS
                         !(fullPair gam pairnames)
                         !(fullRW gam rewritenames)
                         !(fullPrim gam primnames)
                         !(full gam namedirectives)
                         cgdirectives
                         !(full gam trans)
                         !(full gam fexp)
                         !(full gam extra)
    where
      fullPair : Context -> Maybe PairNames -> Core (Maybe PairNames)
      fullPair gam Nothing = pure Nothing
      fullPair gam (Just (MkPairNs t f s))
          = pure $ Just $ MkPairNs !(full gam t) !(full gam f) !(full gam s)

      fullRW : Context -> Maybe RewriteNames -> Core (Maybe RewriteNames)
      fullRW gam Nothing = pure Nothing
      fullRW gam (Just (MkRewriteNs e r))
          = pure $ Just $ MkRewriteNs !(full gam e) !(full gam r)

      fullPrim : Context -> PrimNames -> Core PrimNames
      fullPrim gam (MkPrimNs mi ms mc md)
          = [| MkPrimNs (full gam mi) (full gam ms) (full gam mc) (full gam md) |]


  -- I don't think we ever actually want to call this, because after we read
  -- from the file we're going to add them to learn what the resolved names
  -- are supposed to be! But for completeness, let's do it right.
  resolved gam (MkTTCFile version totalReq sourceHash ifaceHash iHashes incData
                      context userHoles
                      autoHints typeHints
                      imported nextVar currentNS nestedNS
                      pairnames rewritenames primnames
                      namedirectives cgdirectives trans
                      fexp extra)
      = pure $ MkTTCFile version totalReq sourceHash ifaceHash iHashes incData
                         context userHoles
                         !(traverse (resolved gam) autoHints)
                         !(traverse (resolved gam) typeHints)
                         imported nextVar currentNS nestedNS
                         !(resolvedPair gam pairnames)
                         !(resolvedRW gam rewritenames)
                         !(resolvedPrim gam primnames)
                         !(resolved gam namedirectives)
                         cgdirectives
                         !(resolved gam trans)
                         !(resolved gam fexp)
                         !(resolved gam extra)
    where
      resolvedPair : Context -> Maybe PairNames -> Core (Maybe PairNames)
      resolvedPair gam Nothing = pure Nothing
      resolvedPair gam (Just (MkPairNs t f s))
          = pure $ Just $ MkPairNs !(resolved gam t) !(resolved gam f) !(resolved gam s)

      resolvedRW : Context -> Maybe RewriteNames -> Core (Maybe RewriteNames)
      resolvedRW gam Nothing = pure Nothing
      resolvedRW gam (Just (MkRewriteNs e r))
          = pure $ Just $ MkRewriteNs !(resolved gam e) !(resolved gam r)

      resolvedPrim : Context -> PrimNames -> Core PrimNames
      resolvedPrim gam (MkPrimNs mi ms mc md)
          = pure $ MkPrimNs !(resolved gam mi)
                            !(resolved gam ms)
                            !(resolved gam mc)
                            !(resolved gam md)

-- NOTE: TTC files are only compatible if the version number is the same,
-- *and* the 'annot/extra' type are the same, or there are no holes/constraints
writeTTCFile : (HasNames extra, TTC extra) =>
               {auto c : Ref Ctxt Defs} ->
               Ref Bin Binary -> TTCFile extra -> Core ()
writeTTCFile b file_in
      = do file <- toFullNames file_in
           toBuf b "TT2"
           toBuf @{Wasteful} b (version file)
           toBuf b (totalReq file)
           toBuf b (sourceHash file)
           toBuf b (ifaceHash file)
           toBuf b (importHashes file)
           toBuf b (incData file)
           toBuf b (imported file)
           toBuf b (extraData file)
           toBuf b (context file)
           toBuf b (userHoles file)
           toBuf b (autoHints file)
           toBuf b (typeHints file)
           toBuf b (nextVar file)
           toBuf b (currentNS file)
           toBuf b (nestedNS file)
           toBuf b (pairnames file)
           toBuf b (rewritenames file)
           toBuf b (primnames file)
           toBuf b (namedirectives file)
           toBuf b (cgdirectives file)
           toBuf b (transforms file)
           toBuf b (foreignExports file)

readTTCFile : TTC extra =>
              {auto c : Ref Ctxt Defs} ->
              Bool -> String -> Maybe (Namespace) ->
              Ref Bin Binary -> Core (TTCFile extra)
readTTCFile readall file as b
      = do hdr <- fromBuf b
           when (hdr /= "TT2") $
             corrupt ("TTC header in " ++ file ++ " " ++ show hdr)
           ver <- fromBuf @{Wasteful} b
           checkTTCVersion file ver ttcVersion
           totalReq <- fromBuf b
           sourceFileHash <- fromBuf b
           ifaceHash <- fromBuf b
           importHashes <- fromBuf b
           incData <- fromBuf b
           imp <- fromBuf b
           ex <- fromBuf b
           if not readall
              then pure (MkTTCFile ver totalReq
                                   sourceFileHash ifaceHash importHashes
                                   incData [] [] [] [] []
                                   0 (mkNamespace "") [] Nothing
                                   Nothing
                                   (MkPrimNs Nothing Nothing Nothing Nothing)
                                   [] [] [] [] ex)
              else do
                 defs <- fromBuf b
                 uholes <- fromBuf b
                 autohs <- fromBuf b
                 typehs <- fromBuf b
                 nextv <- fromBuf b
                 cns <- fromBuf b
                 nns <- fromBuf b
                 pns <- fromBuf b
                 rws <- fromBuf b
                 prims <- fromBuf b
                 nds <- fromBuf b
                 cgds <- fromBuf b
                 trans <- fromBuf b
                 fexp <- fromBuf b
                 pure (MkTTCFile ver totalReq
                                 sourceFileHash ifaceHash importHashes incData
                                 (map (replaceNS cns) defs) uholes
                                 autohs typehs imp nextv cns nns
                                 pns rws prims nds cgds trans fexp ex)
  where
    -- We don't store full names in 'defs' - we remove the namespace if it's
    -- the same as the current namespace. So, this puts it back.
    replaceNS : Namespace -> (Name, a) -> (Name, a)
    replaceNS ns n@(NS _ _, d) = n
    replaceNS ns (n, d) = (NS ns n, d)

-- Pull out the list of GlobalDefs that we want to save
getSaveDefs : Namespace -> List Name -> List (Name, Binary) -> Defs ->
              Core (List (Name, Binary))
getSaveDefs modns [] acc _ = pure acc
getSaveDefs modns (n :: ns) acc defs
    = do Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => getSaveDefs modns ns acc defs -- 'n' really should exist though!
         -- No need to save builtins
         case definition gdef of
              Builtin _ => getSaveDefs modns ns acc defs
              _ => do bin <- initBinaryS 16384
                      toBuf bin (trimNS modns !(full (gamma defs) gdef))
                      b <- get Bin
                      getSaveDefs modns ns ((trimName (fullname gdef), b) :: acc) defs
  where
    trimName : Name -> Name
    trimName n@(NS defns d) = if defns == modns then d else n
    trimName n = n

-- Write out the things in the context which have been defined in the
-- current source file
export
writeToTTC : (HasNames extra, TTC extra) =>
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             extra -> (sourceFileName : String) ->
             (ttcFileName : String) -> Core ()
writeToTTC extradata sourceFileName ttcFileName
    = do bin <- initBinary
         defs <- get Ctxt
         ust <- get UST
         gdefs <- getSaveDefs (currentNS defs) (keys (toSave defs)) [] defs
         sourceHash <- hashFileWith defs.options.hashFn sourceFileName
         totalReq <- getDefaultTotalityOption
         log "ttc.write" 5 $ unwords
           [ "Writing", ttcFileName
           , "with source hash", show sourceHash
           , "and interface hash", show (ifaceHash defs)
           ]
         writeTTCFile bin
                   (MkTTCFile ttcVersion totalReq
                              sourceHash
                              (ifaceHash defs) (importHashes defs)
                              (incData defs)
                              gdefs
                              (keys (userHoles defs))
                              (saveAutoHints defs)
                              (saveTypeHints defs)
                              (imported defs)
                              (nextName ust)
                              (currentNS defs)
                              (nestedNS defs)
                              (pairnames (options defs))
                              (rewritenames (options defs))
                              (primnames (options defs))
                              (NameMap.toList (namedirectives defs))
                              (cgdirectives defs)
                              (saveTransforms defs)
                              (NameMap.toList (foreignExports defs))
                              extradata)

         Right ok <- coreLift $ writeToFile ttcFileName !(get Bin)
               | Left err => throw (InternalError (ttcFileName ++ ": " ++ show err))
         pure ()

addGlobalDef : {auto c : Ref Ctxt Defs} ->
               (modns : ModuleIdent) -> Namespace ->
               (importAs : Maybe Namespace) ->
               (Name, Binary) -> Core ()
addGlobalDef modns filens asm (n, def)
    = do defs <- get Ctxt
         codedentry <- lookupContextEntry n (gamma defs)
         -- Don't update the coded entry because some names might not be
         -- resolved yet
         entry <- maybe (pure Nothing)
                        (\ p => do x <- decode (gamma defs) (fst p) False (snd p)
                                   pure (Just x))
                        codedentry
         unless (completeDef entry) $
           ignore $ addContextEntry filens n def

         whenJust asm $ \ as => addContextAlias (asName modns as n) n

  where
    -- If the definition already exists, don't overwrite it with an empty
    -- definition or hole. This might happen if a function is declared in one
    -- module and defined in another.
    completeDef : Maybe GlobalDef -> Bool
    completeDef Nothing = False
    completeDef (Just def)
        = case definition def of
               None => False
               Hole _ _ => False
               _ => True

addTypeHint : {auto c : Ref Ctxt Defs} ->
              FC -> (Name, Name, Bool) -> Core ()
addTypeHint fc (tyn, hintn, d)
   = do logC "ttc.read" 10 (pure (show !(getFullName hintn) ++ " for " ++
                            show !(getFullName tyn)))
        addHintFor fc tyn hintn d True

addAutoHint : {auto c : Ref Ctxt Defs} -> (Name, Bool) -> Core ()
addAutoHint (hintn_in, d)
    = do hintn <- toResolvedNames hintn_in
         update Ctxt { autoHints $= insert hintn d }

export
updatePair : {auto c : Ref Ctxt Defs} -> Maybe PairNames -> Core ()
updatePair p = update Ctxt { options->pairnames $= (p <+>) }

export
updateRewrite : {auto c : Ref Ctxt Defs} -> Maybe RewriteNames -> Core ()
updateRewrite r = update Ctxt { options->rewritenames $= (r <+>) }

export
updatePrimNames : PrimNames -> PrimNames -> PrimNames
updatePrimNames p
    = { fromIntegerName $= (p.fromIntegerName <+>),
        fromStringName  $= (p.fromStringName  <+>),
        fromCharName    $= (p.fromCharName    <+>),
        fromDoubleName  $= (p.fromDoubleName  <+>)
      }

export
updatePrims : {auto c : Ref Ctxt Defs} -> PrimNames -> Core ()
updatePrims p = update Ctxt { options->primnames $= updatePrimNames p }

export
updateNameDirectives : {auto c : Ref Ctxt Defs} ->
                       List (Name, List String) -> Core ()
updateNameDirectives [] = pure ()
updateNameDirectives ((t, ns) :: nds)
    = do update Ctxt { namedirectives $= insert t ns }
         updateNameDirectives nds

export
updateCGDirectives : {auto c : Ref Ctxt Defs} ->
                     List (CG, String) -> Core ()
updateCGDirectives cgs = update Ctxt { cgdirectives $= nub . (cgs ++) }

export
updateTransforms : {auto c : Ref Ctxt Defs} ->
                   List (Name, Transform) -> Core ()
updateTransforms [] = pure ()
updateTransforms ((n, t) :: ts)
    = do addT !(toResolvedNames n) !(toResolvedNames t)
         updateTransforms ts
  where
    addT : Name -> Transform -> Core ()
    addT n t
        = do defs <- get Ctxt
             case lookup n (transforms defs) of
                  Nothing =>
                     put Ctxt ({ transforms $= insert n [t] } defs)
                  Just ts =>
                     put Ctxt ({ transforms $= insert n (t :: ts) } defs)

export
updateFExports : {auto c : Ref Ctxt Defs} ->
                 List (Name, (List (String, String))) -> Core ()
updateFExports [] = pure ()
updateFExports ((n, conv) :: ns)
    = do defs <- get Ctxt
         put Ctxt ({ foreignExports $= insert n conv } defs)
         updateFExports ns

getNSas : (String, (ModuleIdent, Bool, Namespace)) ->
          (ModuleIdent, Namespace)
getNSas (a, (b, c, d)) = (b, d)

-- Add definitions from a binary file to the current context
-- Returns the "extra" section of the file (user defined data), the interface
-- hash and the list of additional TTCs that need importing
-- (we need to return these, rather than do it here, because after loading
-- the data that's when we process the extra data...)
export
readFromTTC : TTC extra =>
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              Bool -> -- set nested namespaces (for records, to use at the REPL)
              FC ->
              Bool -> -- importing as public
              (fname : String) -> -- file containing the module
              (modNS : ModuleIdent) -> -- module namespace
              (importAs : Namespace) -> -- namespace to import as
              Core (Maybe (extra, Int,
                           List (ModuleIdent, Bool, Namespace)))
readFromTTC nestedns loc reexp fname modNS importAs
    = do defs <- get Ctxt
         -- If it's already in the context, with the same visibility flag,
         -- don't load it again (we do need to load it again if it's visible
         -- this time, because we need to reexport the dependencies.)
         let False = (modNS, reexp, importAs) `elem` map snd (allImported defs)
              | True => pure Nothing
         put Ctxt ({ allImported $= ((fname, (modNS, reexp, importAs)) :: ) } defs)

         Right buffer <- coreLift $ readFromFile fname
               | Left err => throw (InternalError (fname ++ ": " ++ show err))
         bin <- newRef Bin buffer -- for reading the file into
         let as = if importAs == miAsNamespace modNS
                     then Nothing
                     else Just importAs

         -- If it's already imported, but without reexporting, then all we're
         -- interested in is returning which other modules to load.
         -- Otherwise, add the data
         if alreadyDone modNS importAs (allImported defs)
            then do ttc <- readTTCFile False fname as bin
                    let ex = extraData ttc
                    pure (Just (ex, ifaceHash ttc, imported ttc))
            else do
               ttc <- readTTCFile True fname as bin
               let ex = extraData ttc
               traverse_ (addGlobalDef modNS (currentNS ttc) as) (context ttc)
               traverse_ (addUserHole True) (userHoles ttc)
               setNS (currentNS ttc)
               when nestedns $ setNestedNS (nestedNS ttc)
               -- Only do the next batch if the module hasn't been loaded
               -- in any form
               unless (modNS `elem` map (fst . getNSas) (allImported defs)) $
               -- Set up typeHints and autoHints based on the loaded data
                 do traverse_ (addTypeHint loc) (typeHints ttc)
                    traverse_ addAutoHint (autoHints ttc)
                    addImportedInc modNS (incData ttc)
                    -- Set up pair/rewrite etc names
                    updatePair (pairnames ttc)
                    updateRewrite (rewritenames ttc)
                    updatePrims (primnames ttc)
                    updateNameDirectives (reverse (namedirectives ttc))
                    updateCGDirectives (cgdirectives ttc)
                    updateTransforms (transforms ttc)
                    updateFExports (foreignExports ttc)

               when (not reexp) clearSavedHints
               resetFirstEntry

               -- Finally, update the unification state with the holes from the
               -- ttc
               update UST { nextName := nextVar ttc }
               pure (Just (ex, ifaceHash ttc, imported ttc))
  where
    alreadyDone : ModuleIdent -> Namespace ->
                  List (String, (ModuleIdent, Bool, Namespace)) ->
                  Bool
    alreadyDone modns importAs [] = False
      -- If we've already imported 'modns' as 'importAs', or we're importing
      -- 'modns' as itself and it's already imported as anything, then no
      -- need to load again.
    alreadyDone modns importAs ((_, (m, _, a)) :: rest)
        = (modns == m && importAs == a)
          || (modns == m && miAsNamespace modns == importAs)
          || alreadyDone modns importAs rest

-- Implements a portion of @readTTCFile@. The fields must be read in order.
-- This reads everything up to and including `totalReq`.
export
getTotalReq : String -> Ref Bin Binary -> Core TotalReq
getTotalReq file b
    = do hdr <- fromBuf {a = String} b
         when (hdr /= "TT2") $
           corrupt ("TTC header in " ++ file ++ " " ++ show hdr)
         ver <- fromBuf @{Wasteful} b
         checkTTCVersion file ver ttcVersion
         fromBuf b -- `totalReq`

-- Implements a portion of @readTTCFile@. The fields must be read in order.
-- This reads everything up to and including `interfaceHash`.
export
getHashes : String -> Ref Bin Binary -> Core (Maybe String, Int)
getHashes file b
    = do ignore $ getTotalReq file b
         sourceFileHash <- fromBuf b
         interfaceHash <- fromBuf b
         pure (sourceFileHash, interfaceHash)

-- Implements a portion of @readTTCFile@. The fields must be read in order.
-- This reads everything up to and including `importHashes`.
getImportHashes : String -> Ref Bin Binary ->
                  Core (List (Namespace, Int))
getImportHashes file b
    = do ignore $ getHashes file b
         fromBuf b -- `importHashes`

-- Implements a portion of @readTTCFile@. The fields must be read in order.
-- This reads everything up to and including `incData`.
getIncData : String -> Ref Bin Binary ->
             Core (List (CG, String, List String))
getIncData file b
    = do ignore $ getImportHashes file b
         fromBuf b -- `incData`

export
readTotalReq : (fileName : String) -> -- file containing the module
               Core (Maybe TotalReq)
readTotalReq fileName
    = do Right buffer <- coreLift $ readFromFile fileName
            | Left err => pure Nothing
         b <- newRef Bin buffer
         catch (Just <$> getTotalReq fileName b)
               (\err => pure Nothing)

export
readHashes : (fileName : String) -> -- file containing the module
                Core (Maybe String, Int)
readHashes fileName
    = do Right buffer <- coreLift $ readFromFile fileName
            | Left err => pure (Nothing, 0)
         b <- newRef Bin buffer
         catch (getHashes fileName b)
               (\err => pure (Nothing, 0))

export
readImportHashes : (fname : String) -> -- file containing the module
                   Core (List (Namespace, Int))
readImportHashes fname
    = do Right buffer <- coreLift $ readFromFile fname
            | Left err => pure []
         b <- newRef Bin buffer
         catch (do res <- getImportHashes fname b
                   pure res)
               (\err => pure [])

export
readIncData : (fname : String) -> -- file containing the module
              Core (List (CG, String, List String))
readIncData fname
    = do Right buffer <- coreLift $ readFromFile fname
            | Left err => pure []
         b <- newRef Bin buffer
         catch (do res <- getIncData fname b
                   pure res)
               (\err => pure [])
