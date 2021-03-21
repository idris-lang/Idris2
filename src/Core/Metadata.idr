module Core.Metadata

import Core.Binary
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.FC
import Core.Normalise
import Core.TT
import Core.TTC

import Data.List
import System.File
import Libraries.Data.PosMap
import Libraries.Utils.Binary

%default covering

-- Additional data we keep about the context to support interactive editing

public export
record Metadata where
       constructor MkMetadata
       -- Mapping from source annotation (location, typically) to
       -- the LHS defined at that location. Also record the outer environment
       -- length, since we don't want to case split on these.
       lhsApps : List (NonEmptyFC, (Nat, ClosedTerm))
       -- Mapping from annotation to the name defined with that annotation,
       -- and its type (so, giving the ability to get the types of locally
       -- defined names)
       -- The type is abstracted over the whole environment; the Nat gives
       -- the number of names which were in the environment at the time.
       names : List (NonEmptyFC, (Name, Nat, ClosedTerm))
       -- Mapping from annotation to the name that's declared there and
       -- its type; the Nat is as above
       tydecls : List (NonEmptyFC, (Name, Nat, ClosedTerm))
       -- Current lhs, if applicable, and a mapping from hole names to the
       -- lhs they're under. This is for expression search, to ensure that
       -- recursive calls have a smaller value as an argument.
       -- Also use this to get the name of the function being defined (i.e.
       -- to know what the recursive call is, if applicable)
       currentLHS : Maybe ClosedTerm
       holeLHS : List (Name, ClosedTerm)
       nameLocMap : PosMap (NonEmptyFC, Name)

Show Metadata where
  show (MkMetadata apps names tydecls currentLHS holeLHS nameLocMap)
    = "Metadata:\n" ++
      " lhsApps: " ++ show apps ++ "\n" ++
      " names: " ++ show names ++ "\n" ++
      " type declarations: " ++ show tydecls ++ "\n" ++
      " current LHS: " ++ show currentLHS ++ "\n" ++
      " holes: " ++ show holeLHS ++ "\n" ++
      " nameLocMap: " ++ show nameLocMap

export
initMetadata : Metadata
initMetadata = MkMetadata
  { lhsApps = []
  , names = []
  , tydecls = []
  , currentLHS = Nothing
  , holeLHS = []
  , nameLocMap = empty
  }

-- A label for metadata in the global state
export
data MD : Type where

TTC Metadata where
  toBuf b m
      = do toBuf b (lhsApps m)
           toBuf b (names m)
           toBuf b (tydecls m)
           toBuf b (holeLHS m)
           toBuf b (nameLocMap m)

  fromBuf b
      = do apps <- fromBuf b
           ns <- fromBuf b
           tys <- fromBuf b
           hlhs <- fromBuf b
           dlocs <- fromBuf b
           pure (MkMetadata apps ns tys Nothing hlhs dlocs)

export
addLHS : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         {auto m : Ref MD Metadata} ->
         FC -> Nat -> Env Term vars -> Term vars -> Core ()
addLHS loc outerenvlen env tm
    = do meta <- get MD
         tm' <- toFullNames (bindEnv loc (toPat env) tm)
         -- Put the lhs on the metadata if it's not empty
         whenJust (isNonEmptyFC loc) $ \ neloc =>
           put MD $ record { lhsApps $= ((neloc, outerenvlen, tm') ::) } meta

  where
    toPat : Env Term vs -> Env Term vs
    toPat (Lam fc c p ty :: bs) = PVar fc c p ty :: toPat bs
    toPat (b :: bs) = b :: toPat bs
    toPat [] = []

-- For giving local variable names types, just substitute the name
-- rather than storing the whole environment, otherwise we'll repeatedly
-- store the environment and it'll get big.
-- We'll need to rethink a bit if we want interactive editing to show
-- the whole environment - perhaps store each environment just once
-- along with its source span?
-- In any case, one could always look at the other names to get their
-- types directly!
substEnv : {vars : _} ->
           FC -> Env Term vars -> (tm : Term vars) -> ClosedTerm
substEnv loc [] tm = tm
substEnv {vars = x :: _} loc (b :: env) tm
    = substEnv loc env (subst (Ref loc Bound x) tm)

export
addNameType : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              FC -> Name -> Env Term vars -> Term vars -> Core ()
addNameType loc n env tm
    = do meta <- get MD
         n' <- getFullName n

         -- Add the name to the metadata if the file context is not empty
         whenJust (isNonEmptyFC loc) $ \ neloc => do
           put MD $ record { names $= ((neloc, (n', 0, substEnv loc env tm)) ::) } meta
           log "metadata.names" 7 $ show n' ++ " at line " ++ show (1 + startLine neloc)

export
addTyDecl : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            FC -> Name -> Env Term vars -> Term vars -> Core ()
addTyDecl loc n env tm
    = do meta <- get MD
         n' <- getFullName n

         -- Add the type declaration to the metadata if the file context is not empty
         whenJust (isNonEmptyFC loc) $ \ neloc =>
           put MD $ record { tydecls $= ( (neloc, (n', length env, bindEnv loc env tm)) ::) } meta

export
addNameLoc : {auto m : Ref MD Metadata} ->
             {auto c : Ref Ctxt Defs} ->
             FC -> Name -> Core ()
addNameLoc loc n
    = do meta <- get MD
         n' <- getFullName n
         whenJust (isNonEmptyFC loc) $ \neloc =>
           put MD $ record { nameLocMap $= insert (neloc, n') } meta

export
setHoleLHS : {auto m : Ref MD Metadata} ->
             ClosedTerm -> Core ()
setHoleLHS tm
    = do meta <- get MD
         put MD (record { currentLHS = Just tm } meta)

export
clearHoleLHS : {auto m : Ref MD Metadata} ->
               Core ()
clearHoleLHS
    = do meta <- get MD
         put MD (record { currentLHS = Nothing } meta)

export
withCurrentLHS : {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 Name -> Core ()
withCurrentLHS n
    = do meta <- get MD
         n' <- getFullName n
         maybe (pure ())
               (\lhs => put MD (record { holeLHS $= ((n', lhs) ::) } meta))
               (currentLHS meta)

findEntryWith : (NonEmptyFC -> a -> Bool) -> List (NonEmptyFC, a) -> Maybe (NonEmptyFC, a)
findEntryWith = find . uncurry

export
findLHSAt : {auto m : Ref MD Metadata} ->
            (NonEmptyFC -> ClosedTerm -> Bool) ->
            Core (Maybe (NonEmptyFC, Nat, ClosedTerm))
findLHSAt p
    = do meta <- get MD
         pure (findEntryWith (\ loc, tm => p loc (snd tm)) (lhsApps meta))

export
findTypeAt : {auto m : Ref MD Metadata} ->
             (NonEmptyFC -> (Name, Nat, ClosedTerm) -> Bool) ->
             Core (Maybe (Name, Nat, ClosedTerm))
findTypeAt p
    = do meta <- get MD
         pure (map snd (findEntryWith p (names meta)))

export
findTyDeclAt : {auto m : Ref MD Metadata} ->
               (NonEmptyFC -> (Name, Nat, ClosedTerm) -> Bool) ->
               Core (Maybe (NonEmptyFC, Name, Nat, ClosedTerm))
findTyDeclAt p
    = do meta <- get MD
         pure (findEntryWith p (tydecls meta))

export
findHoleLHS : {auto m : Ref MD Metadata} ->
              Name -> Core (Maybe ClosedTerm)
findHoleLHS hn
    = do meta <- get MD
         pure (lookupBy (\x, y => dropNS x == dropNS y) hn (holeLHS meta))

-- Normalise all the types of the names, since they might have had holes
-- when added and the holes won't necessarily get saved
normaliseTypes : {auto m : Ref MD Metadata} ->
                 {auto c : Ref Ctxt Defs} ->
                 Core ()
normaliseTypes
    = do meta <- get MD
         defs <- get Ctxt
         ns' <- traverse (nfType defs) (names meta)
         put MD (record { names = ns' } meta)
  where
    nfType : Defs -> (NonEmptyFC, (Name, Nat, ClosedTerm)) ->
             Core (NonEmptyFC, (Name, Nat, ClosedTerm))
    nfType defs (loc, (n, len, ty))
       = pure (loc, (n, len, !(normaliseArgHoles defs [] ty)))

record TTMFile where
  constructor MkTTMFile
  version : Int
  metadata : Metadata

TTC TTMFile where
  toBuf b file
      = do toBuf b "TTM"
           toBuf b (version file)
           toBuf b (metadata file)

  fromBuf b
      = do hdr <- fromBuf b
           when (hdr /= "TTM") $ corrupt "TTM header"
           ver <- fromBuf b
           checkTTCVersion "" ver ttcVersion -- maybe change the interface to get the filename
           md <- fromBuf b
           pure (MkTTMFile ver md)

HasNames Metadata where
  full gam (MkMetadata lhs ns tys clhs hlhs dlocs)
      = pure $ MkMetadata !(traverse fullLHS lhs)
                          !(traverse fullTy ns)
                          !(traverse fullTy tys)
                          Nothing
                          !(traverse fullHLHS hlhs)
                          (fromList !(traverse fullDecls (toList dlocs)))
    where
      fullLHS : (NonEmptyFC, (Nat, ClosedTerm)) -> Core (NonEmptyFC, (Nat, ClosedTerm))
      fullLHS (fc, (i, tm)) = pure (fc, (i, !(full gam tm)))

      fullTy : (NonEmptyFC, (Name, Nat, ClosedTerm)) -> Core (NonEmptyFC, (Name, Nat, ClosedTerm))
      fullTy (fc, (n, i, tm)) = pure (fc, (!(full gam n), i, !(full gam tm)))

      fullHLHS : (Name, ClosedTerm) -> Core (Name, ClosedTerm)
      fullHLHS (n, tm) = pure (!(full gam n), !(full gam tm))

      fullDecls : (NonEmptyFC, Name) -> Core (NonEmptyFC, Name)
      fullDecls (fc, n) = pure (fc, !(full gam n))

  resolved gam (MkMetadata lhs ns tys clhs hlhs dlocs)
      = pure $ MkMetadata !(traverse resolvedLHS lhs)
                          !(traverse resolvedTy ns)
                          !(traverse resolvedTy tys)
                          Nothing
                          !(traverse resolvedHLHS hlhs)
                          (fromList !(traverse resolvedDecls (toList dlocs)))
    where
      resolvedLHS : (NonEmptyFC, (Nat, ClosedTerm)) -> Core (NonEmptyFC, (Nat, ClosedTerm))
      resolvedLHS (fc, (i, tm)) = pure (fc, (i, !(resolved gam tm)))

      resolvedTy : (NonEmptyFC, (Name, Nat, ClosedTerm)) -> Core (NonEmptyFC, (Name, Nat, ClosedTerm))
      resolvedTy (fc, (n, i, tm)) = pure (fc, (!(resolved gam n), i, !(resolved gam tm)))

      resolvedHLHS : (Name, ClosedTerm) -> Core (Name, ClosedTerm)
      resolvedHLHS (n, tm) = pure (!(resolved gam n), !(resolved gam tm))

      resolvedDecls : (NonEmptyFC, Name) -> Core (NonEmptyFC, Name)
      resolvedDecls (fc, n) = pure (fc, !(resolved gam n))

export
writeToTTM : {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             (fname : String) ->
             Core ()
writeToTTM fname
    = do normaliseTypes
         buf <- initBinary
         meta <- get MD
         defs <- get Ctxt
         toBuf buf (MkTTMFile ttcVersion !(full (gamma defs) meta))
         Right ok <- coreLift $ writeToFile fname !(get Bin)
             | Left err => throw (InternalError (fname ++ ": " ++ show err))
         pure ()

export
readFromTTM : {auto m : Ref MD Metadata} ->
              (fname : String) ->
              Core ()
readFromTTM fname
    = do Right buf <- coreLift $ readFromFile fname
             | Left err => throw (InternalError (fname ++ ": " ++ show err))
         bin <- newRef Bin buf
         ttm <- fromBuf bin
         put MD (metadata ttm)

||| Read Metadata from given file
export
readMetadata : (fname : String) -> Core Metadata
readMetadata fname
  = do Right buf <- coreLift $ readFromFile fname
             | Left err => throw (InternalError (fname ++ ": " ++ show err))
       bin <- newRef Bin buf
       MkTTMFile _ md <- fromBuf bin
       pure md

||| Dump content of a .ttm file in human-readable format
export
dumpTTM : (filename : String) -> Core ()
dumpTTM fname
    = do md <- readMetadata fname
         coreLift $ putStrLn $ show md
