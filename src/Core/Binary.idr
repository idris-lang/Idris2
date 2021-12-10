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
import Data.List1
import Data.String
import Data.These

import System.File

import Libraries.Data.NameMap

import public Libraries.Utils.Binary

%default covering

||| TTC files can only be compatible if the version number is the same
||| (Increment this when changing anything in the data format)
export
ttcVersion : Int
ttcVersion = 71

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
  imported : List (ModuleIdent, Bool, Namespace, Maybe ImportDirective)
  nextVar : Int
  currentNS : Namespace
  nestedNS : List Namespace
  pairnames : Maybe PairNames
  rewritenames : Maybe RewriteNames
  primnames : PrimNames
  namedirectives : List (Name, List String)
  cgdirectives : List (CG, String)
  transforms : List (Name, Transform)
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

HasNames (Name, List String) where
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
                      extra)
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
                      extra)
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

readTTCFile : TTC extra =>
              {auto c : Ref Ctxt Defs} ->
              Bool -> String ->
              Ref Bin Binary -> Core (TTCFile extra)
readTTCFile readall file b
      = do hdr <- fromBuf b
           chunk <- get Bin
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
                                   [] [] [] ex)
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
                 pure (MkTTCFile ver totalReq
                                 sourceFileHash ifaceHash importHashes incData
                                 (map (replaceNS cns) defs) uholes
                                 autohs typehs imp nextv cns nns
                                 pns rws prims nds cgds trans ex)
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

addAutoHint : {auto c : Ref Ctxt Defs} ->
              (Name, Bool) -> Core ()
addAutoHint (hintn_in, d)
    = do defs <- get Ctxt
         hintn <- toResolvedNames hintn_in

         put Ctxt (record { autoHints $= insert hintn d } defs)

export
updatePair : {auto c : Ref Ctxt Defs} ->
             Maybe PairNames -> Core ()
updatePair p
    = do defs <- get Ctxt
         put Ctxt (record { options->pairnames $= (p <+>) } defs)

export
updateRewrite : {auto c : Ref Ctxt Defs} ->
                Maybe RewriteNames -> Core ()
updateRewrite r
    = do defs <- get Ctxt
         put Ctxt (record { options->rewritenames $= (r <+>) } defs)

export
updatePrimNames : PrimNames -> PrimNames -> PrimNames
updatePrimNames p
    = record { fromIntegerName $= ((fromIntegerName p) <+>),
               fromStringName $= ((fromStringName p) <+>),
               fromCharName $= ((fromCharName p) <+>),
               fromDoubleName $= ((fromDoubleName p) <+>)
             }

export
updatePrims : {auto c : Ref Ctxt Defs} ->
              PrimNames -> Core ()
updatePrims p
    = do defs <- get Ctxt
         put Ctxt (record { options->primnames $= updatePrimNames p } defs)

export
updateNameDirectives : {auto c : Ref Ctxt Defs} ->
                       List (Name, List String) -> Core ()
updateNameDirectives [] = pure ()
updateNameDirectives ((t, ns) :: nds)
    = do defs <- get Ctxt
         put Ctxt (record { namedirectives $= insert t ns } defs)
         updateNameDirectives nds

export
updateCGDirectives : {auto c : Ref Ctxt Defs} ->
                     List (CG, String) -> Core ()
updateCGDirectives cgs
    = do defs <- get Ctxt
         let cgs' = nub (cgs ++ cgdirectives defs)
         put Ctxt (record { cgdirectives = cgs' } defs)

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
                     put Ctxt (record { transforms $= insert n [t] } defs)
                  Just ts =>
                     put Ctxt (record { transforms $= insert n (t :: ts) } defs)


getNSas : (String, (ModuleIdent, Bool, Namespace)) ->
          (ModuleIdent, Namespace)
getNSas (a, (b, c, d)) = (b, d)

addUsedGlobalDefs :
  {auto c : Ref Ctxt Defs} ->
  List (Name, Binary) ->
  ModuleIdent ->
  (cns : Namespace) ->
  (as : Maybe Namespace) ->
  ImportDirective ->
  Core ()
addUsedGlobalDefs defs modNS cns as dir
  = do (ures, uren) <- go [] [] (fromThis dir) (forget <$> fromThat dir) defs
       -- Complain when we have restrictions that do not match any of the
       -- declarations present in the module
       whenCons ures $ \ x, xs =>
         recordWarning
         $ GenericWarn
         $ "Could not find requested names in module \{show modNS}: "
         ++ showSep "," (map show (x :: xs))
       -- Complain when we have renaming rules that do not match any of the
       -- declarations present in the module
       whenCons uren $ \ x, xs =>
         recordWarning
         $ GenericWarn
         $ "Could not find requested names in module \{show modNS}: "
         ++ showSep "," (map (show . fst) (x :: xs))

  where

  shouldKeep : Name -> ImportRestriction -> (Bool, Maybe Name)
  shouldKeep entry (Using includes)
    = let check = find (\ nm => nameRoot nm == nameRoot entry
                             && matches nm entry)
                       (forget includes)
      in (isJust check, check)
  shouldKeep entry (Hiding excludes)
    = let check = find (\ nm => nameRoot nm == nameRoot entry
                             && matches nm entry)
                       (forget excludes)
      in (isNothing check, check)

  shouldRename : Name -> List (Name, Name) -> Maybe (Name, Name)
  shouldRename entry renamings
    = find (\ (src, _) => nameRoot src == nameRoot entry
                       && matches src entry)
           renamings

  go : List Name -> List (Name, Name) ->
       Maybe ImportRestriction ->
       Maybe (List (Name, Name)) ->
       List (Name, Binary) -> Core (List Name, List (Name, Name))
  go ures uren mres mren [] =
    let res = case mres of
                Nothing => []
                Just (Using nms) => forget nms
                Just (Hiding nms) => forget nms
        ren = fromMaybe [] mren
    in pure (res \\ ures, ren \\ uren)
  go ures uren mres mren (entry@(entryName, entryCode) :: defs) =
    let check : (Bool, Maybe Name)
      --         ^      ^--- whether this decision was caused by a rule
      --          `---- whether to keep the definition
      -- So (True, Just _)  means a `using` led to this being kept
      --    (True, Nothing) means it's due to not being caught by a `hiding`
      := maybe (True, Nothing) (shouldKeep entryName) mres
    in case check of
      -- filtered in
      (True, Just nm) => do addGlobalDef modNS cns as entry
                            go (nm :: ures) uren mres mren defs
      -- filtered out
      (False, Just nm) => go (nm :: ures) uren mres mren defs
      -- falling through: is it renamed? In which case it may be retained.
      -- Indeed in `import A using (b) renaming (c to d)` we should still
      -- re-export c as d even though it's not in `using`!
      (b, Nothing) => do
        let check : Maybe (Name, Name) := shouldRename entryName =<< mren
        let Just r@(src, tgt) = check
              | Nothing => do when b $ addGlobalDef modNS cns as entry
                              go ures uren mres mren defs
        addGlobalDef modNS cns as (tgt, entryCode)
        go ures (r :: uren) mres mren defs

||| Add definitions from a binary file to the current context
||| @ nestedns Set nested namespaces (for records, to use at the REPL)
||| @ publicly Importing as public
||| @ fname    File containing the module
||| @ modNS    Module namespace
||| @ importAs Namespace to import as
||| @ imports  Explicit list of names to import (optional)
|||
||| Also returns
||| 1. the extra section of the file (user defined data)
||| 2. the interface hash
||| 3. and the list of additional TTCs that need importing
-- (we need to return these, rather than do it here, because after loading
-- the data that's when we process the extra data...)
export
readFromTTC : TTC extra =>
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              (nestedns : Bool) ->
              FC ->
              (publicly : Bool) ->
              (fname : String) ->
              (modNS : ModuleIdent) ->
              (importAs : Namespace) ->
              (imports : Maybe ImportDirective) ->
              Core (Maybe (extra, Int,
                           List (ModuleIdent, Bool, Namespace, Maybe ImportDirective)))
readFromTTC nestedns loc reexp fname modNS importAs imports
    = do defs <- get Ctxt
         -- If it's already in the context, with the same visibility flag,
         -- don't load it again (we do need to load it again if it's visible
         -- this time, because we need to reexport the dependencies.)
         let False = (modNS, reexp, importAs) `elem` map snd (allImported defs)
              | True => pure Nothing
         put Ctxt (record { allImported $= ((fname, (modNS, reexp, importAs)) :: ) } defs)

         Right buffer <- coreLift $ readFromFile fname
               | Left err => throw (InternalError (fname ++ ": " ++ show err))
         bin <- newRef Bin buffer -- for reading the file into
         let as = importAs <$ guard (importAs /= miAsNamespace modNS)

         -- If it's already imported, but without reexporting, then all we're
         -- interested in is returning which other modules to load.
         -- Otherwise, add the data
         if alreadyDone modNS importAs (allImported defs)
            then do ttc <- readTTCFile False fname bin
                    let ex = extraData ttc
                    pure (Just (ex, ifaceHash ttc, imported ttc))
            else do
               ttc <- readTTCFile True fname bin
               let ex = extraData ttc
               elim_ imports
                 (for_ (context ttc) (addGlobalDef modNS (currentNS ttc) as))
                 (addUsedGlobalDefs (context ttc) modNS (currentNS ttc) as)
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
                    defs <- get Ctxt
                    -- Set up pair/rewrite etc names
                    updatePair (pairnames ttc)
                    updateRewrite (rewritenames ttc)
                    updatePrims (primnames ttc)
                    updateNameDirectives (reverse (namedirectives ttc))
                    updateCGDirectives (cgdirectives ttc)
                    updateTransforms (transforms ttc)

               when (not reexp) clearSavedHints
               resetFirstEntry

               -- Finally, update the unification state with the holes from the
               -- ttc
               ust <- get UST
               put UST (record { nextName = nextVar ttc } ust)
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

getImportHashes : String -> Ref Bin Binary ->
                  Core (List (Namespace, Int))
getImportHashes file b
    = do hdr <- fromBuf {a = String} b
         when (hdr /= "TT2") $ corrupt ("TTC header in " ++ file ++ " " ++ show hdr)
         ver <- fromBuf @{Wasteful} b
         checkTTCVersion file ver ttcVersion
         totalReq <- fromBuf {a = TotalReq} b
         sourceFileHash <- fromBuf {a = Maybe String} b
         interfaceHash <- fromBuf {a = Int} b
         fromBuf b

export
getTotalReq : String -> Ref Bin Binary -> Core TotalReq
getTotalReq file b
    = do hdr <- fromBuf {a = String} b
         when (hdr /= "TT2") $ corrupt ("TTC header in " ++ file ++ " " ++ show hdr)
         ver <- fromBuf @{Wasteful} b
         checkTTCVersion file ver ttcVersion
         fromBuf b

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
getHashes : String -> Ref Bin Binary -> Core (Maybe String, Int)
getHashes file b
    = do hdr <- fromBuf {a = String} b
         when (hdr /= "TT2") $ corrupt ("TTC header in " ++ file ++ " " ++ show hdr)
         ver <- fromBuf @{Wasteful} b
         checkTTCVersion file ver ttcVersion
         totReq <- fromBuf {a = TotalReq} b
         sourceFileHash <- fromBuf b
         interfaceHash <- fromBuf b
         pure (sourceFileHash, interfaceHash)

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
