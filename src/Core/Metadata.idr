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

import public Protocol.IDE.Decoration as Protocol.IDE

%default covering

export
nameDecoration : Name -> NameType -> Decoration
nameDecoration nm nt
  = ifThenElse (isUnsafeBuiltin nm) Postulate (nameTypeDecoration nt)

  where

  nameTypeDecoration : NameType -> Decoration
  nameTypeDecoration Bound         = Bound
  nameTypeDecoration Func          = Function
  nameTypeDecoration (DataCon _ _) = Data
  nameTypeDecoration (TyCon _ _  ) = Typ


public export
ASemanticDecoration : Type
ASemanticDecoration = (NonEmptyFC, Decoration, Maybe Name)

public export
SemanticDecorations : Type
SemanticDecorations = List ASemanticDecoration

TTC Decoration where
  toBuf b Typ       = tag 0
  toBuf b Function  = tag 1
  toBuf b Data      = tag 2
  toBuf b Keyword   = tag 3
  toBuf b Bound     = tag 4
  toBuf b Namespace = tag 5
  toBuf b Postulate = tag 6
  toBuf b Module    = tag 7
  toBuf b Comment   = tag 8
  fromBuf b
    = case !getTag of
        0 => pure Typ
        1 => pure Function
        2 => pure Data
        3 => pure Keyword
        4 => pure Bound
        5 => pure Namespace
        6 => pure Postulate
        7 => pure Module
        8 => pure Comment
        _ => corrupt "Decoration"

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
       sourceIdent : OriginDesc

       ||| Semantic Highlighting
       ||| Posmap of known semantic decorations
       semanticHighlighting : PosMap ASemanticDecoration

       ||| Posmap of aliases (in `with` clauses the LHS disapear during
       ||| elaboration after making sure that they match their parents'
       semanticAliases : PosMap (NonEmptyFC, NonEmptyFC)

       ||| Posmap of decorations to default to if the elaboration does not
       ||| produce any highlighting for this range
       semanticDefaults : PosMap ASemanticDecoration


||| Combine semanticHighlighting, semanticAliases, and semanticDefaults into
||| a single posmap with all the information
export
allSemanticHighlighting :
  {auto c : Ref Ctxt Defs} ->
  Metadata -> Core (PosMap ASemanticDecoration)
allSemanticHighlighting meta = do
    let semHigh = meta.semanticHighlighting
    log "ide-mode.highlight" 19 $
      "Semantic metadata is: " ++ show semHigh

    let aliases
          : List ASemanticDecoration
          = flip foldMap meta.semanticAliases $ \ (from, to) =>
              let decors = uncurry exactRange (snd to) semHigh in
              map (\ ((fnm, loc), rest) => ((fnm, snd from), rest)) decors
    log "ide-mode.highlight.alias" 19 $
      "Semantic metadata from aliases is: " ++ show aliases

    let defaults
         : List ASemanticDecoration
         = flip foldMap meta.semanticDefaults $ \ decor@((_, range), _) =>
             case uncurry exactRange range semHigh of
               [] => [decor]
               _ => []

    pure (fromList aliases `union` (fromList defaults `union` semHigh))

covering
Show Metadata where
  show (MkMetadata apps names tydecls currentLHS holeLHS nameLocMap
                   fname semanticHighlighting semanticAliases semanticDefaults) = """
    Metadata:
     lhsApps: \{ show apps }
     names: \{ show names }
     type declarations: \{ show tydecls }
     current LHS: \{ show currentLHS }
     holes: \{ show holeLHS }
     nameLocMap: \{ show nameLocMap }
     sourceIdent: \{ show fname }
     semanticHighlighting: \{ show semanticHighlighting }
     semanticAliases: \{ show semanticAliases }
     semanticDefaults: \{ show semanticDefaults }
    """

export
initMetadata : OriginDesc -> Metadata
initMetadata finfo = MkMetadata
  { lhsApps = []
  , names = []
  , tydecls = []
  , currentLHS = Nothing
  , holeLHS = []
  , nameLocMap = empty
  , sourceIdent = finfo
  , semanticHighlighting = empty
  , semanticAliases = empty
  , semanticDefaults = empty
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
           toBuf b (sourceIdent m)
           toBuf b (semanticHighlighting m)
           toBuf b (semanticAliases m)
           toBuf b (semanticDefaults m)

  fromBuf b
      = do apps <- fromBuf b
           ns <- fromBuf b
           tys <- fromBuf b
           hlhs <- fromBuf b
           dlocs <- fromBuf b
           fname <- fromBuf b
           semhl <- fromBuf b
           semal <- fromBuf b
           semdef <- fromBuf b
           pure (MkMetadata apps ns tys Nothing hlhs dlocs fname semhl semal semdef)

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
           put MD $ { lhsApps $= ((neloc, outerenvlen, tm') ::) } meta

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
         whenJust (isConcreteFC loc) $ \ neloc => do
           put MD $ { names $= ((neloc, (n', 0, substEnv loc env tm)) ::) } meta
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
           put MD $ { tydecls $= ( (neloc, (n', length env, bindEnv loc env tm)) ::) } meta

export
addNameLoc : {auto m : Ref MD Metadata} ->
             {auto c : Ref Ctxt Defs} ->
             FC -> Name -> Core ()
addNameLoc loc n
    = do meta <- get MD
         n' <- getFullName n
         whenJust (isConcreteFC loc) $ \neloc =>
           put MD $ { nameLocMap $= insert (neloc, n') } meta

export
setHoleLHS : {auto m : Ref MD Metadata} -> ClosedTerm -> Core ()
setHoleLHS tm = update MD { currentLHS := Just tm }

export
clearHoleLHS : {auto m : Ref MD Metadata} -> Core ()
clearHoleLHS = update MD { currentLHS := Nothing }

export
withCurrentLHS : {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 Name -> Core ()
withCurrentLHS n
    = do meta <- get MD
         n' <- getFullName n
         maybe (pure ())
               (\lhs => put MD ({ holeLHS $= ((n', lhs) ::) } meta))
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

export
addSemanticDefault : {auto m : Ref MD Metadata} ->
                     ASemanticDecoration -> Core ()
addSemanticDefault asem = update MD { semanticDefaults $= insert asem }

export
addSemanticAlias : {auto m : Ref MD Metadata} ->
                   NonEmptyFC -> NonEmptyFC -> Core ()
addSemanticAlias from to = update MD { semanticAliases $= insert (from, to) }

export
addSemanticDecorations : {auto m : Ref MD Metadata} ->
                         {auto c : Ref Ctxt Defs} ->
   SemanticDecorations -> Core ()
addSemanticDecorations decors
    = do meta <- get MD
         let posmap = meta.semanticHighlighting
         let (newDecors,droppedDecors) =
               span
                 ( (meta.sourceIdent ==)
                 . Builtin.fst
                 . Builtin.fst )
                 decors
         unless (isNil droppedDecors)
           $ log "ide-mode.highlight" 19 $ "ignored adding decorations to "
               ++ show meta.sourceIdent ++ ": " ++ show droppedDecors
         put MD $ {semanticHighlighting
                     := (fromList newDecors) `union` posmap} meta


-- Normalise all the types of the names, since they might have had holes
-- when added and the holes won't necessarily get saved
normaliseTypes : {auto m : Ref MD Metadata} ->
                 {auto c : Ref Ctxt Defs} ->
                 Core ()
normaliseTypes
    = do meta <- get MD
         defs <- get Ctxt
         ns' <- traverse (nfType defs) (names meta)
         put MD ({ names := ns' } meta)
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
  full gam md
      = pure $ { lhsApps := !(traverse fullLHS $ md.lhsApps)
               , names   := !(traverse fullTy $ md.names)
               , tydecls := !(traverse fullTy $ md.tydecls)
               , currentLHS := Nothing
               , holeLHS := !(traverse fullHLHS $ md.holeLHS)
               , nameLocMap := fromList !(traverse fullDecls (toList $ md.nameLocMap))
               } md
    where
      fullLHS : (NonEmptyFC, (Nat, ClosedTerm)) -> Core (NonEmptyFC, (Nat, ClosedTerm))
      fullLHS (fc, (i, tm)) = pure (fc, (i, !(full gam tm)))

      fullTy : (NonEmptyFC, (Name, Nat, ClosedTerm)) -> Core (NonEmptyFC, (Name, Nat, ClosedTerm))
      fullTy (fc, (n, i, tm)) = pure (fc, (!(full gam n), i, !(full gam tm)))

      fullHLHS : (Name, ClosedTerm) -> Core (Name, ClosedTerm)
      fullHLHS (n, tm) = pure (!(full gam n), !(full gam tm))

      fullDecls : (NonEmptyFC, Name) -> Core (NonEmptyFC, Name)
      fullDecls (fc, n) = pure (fc, !(full gam n))

  resolved gam (MkMetadata lhs ns tys clhs hlhs dlocs fname semhl semal semdef)
      = pure $ MkMetadata !(traverse resolvedLHS lhs)
                          !(traverse resolvedTy ns)
                          !(traverse resolvedTy tys)
                          Nothing
                          !(traverse resolvedHLHS hlhs)
                          (fromList !(traverse resolvedDecls (toList dlocs)))
                          fname
                          semhl
                          semal
                          semdef
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
