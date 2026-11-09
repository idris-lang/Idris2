module TTImp.Elab.Record

import Core.Env
import Core.Metadata
import Core.Unify
import Core.Value

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.TTImp

import Data.SortedSet
import Data.SnocList

%default covering

getRecordType : Env Term vars -> NF vars -> Maybe Name
getRecordType env (NTCon _ n _ _) = Just n
getRecordType env _ = Nothing

getNames : {auto c : Ref Ctxt Defs} -> Defs -> ClosedNF -> Core $ SortedSet Name
getNames defs (NApp _ hd args)
    = do eargs <- traverse (evalClosure defs . snd) args
         pure $ nheadNames hd `union` concat !(traverse (getNames defs) eargs)
  where
    nheadNames : NHead Scope.empty -> SortedSet Name
    nheadNames (NRef Bound n) = singleton n
    nheadNames _ = empty
getNames defs (NDCon _ _ _ _ args)
    = do eargs <- traverse (evalClosure defs . snd) args
         pure $ concat !(traverse (getNames defs) eargs)
getNames defs (NTCon _ _ _ args)
  = do eargs <- traverse (evalClosure defs . snd) args
       pure $ concat !(traverse (getNames defs) eargs)
getNames defs (NDelayed _ _ tm) = getNames defs tm
getNames {} = pure empty

data Rec : Type where
     Field : Maybe Name -> -- implicit argument name, if any
             String -> RawImp -> Rec -- field name on left, value on right
     Constr : Maybe Name -> -- implicit argument name, if any
              Name -> List (String, Rec) -> Rec

covering
Show Rec where
  show (Field mn n ty)
      = "Field " ++ show mn ++ "; " ++ show n ++ " : " ++ show ty
  show (Constr mn n args)
      = "Constr " ++ show mn ++ " " ++ show n ++ " " ++ show args

toLHS' : FC -> Rec -> (Maybe Name, RawImp)
toLHS' loc (Field mn@(Just _) n _)
    = (mn, IAs loc (virtualiseFC loc) UseRight (UN $ Basic n) (Implicit loc True))
toLHS' loc (Field mn n _) = (mn, IBindVar (virtualiseFC loc) (UN $ Basic n))
toLHS' loc (Constr mn con args)
    = let args' = map (toLHS' loc . snd) args in
          (mn, gapply (IVar loc con) args')

toLHS : FC -> Rec -> RawImp
toLHS fc r = snd (toLHS' fc r)

toRHS' : FC -> Rec -> (Maybe Name, RawImp)
toRHS' loc (Field mn _ val) = (mn, val)
toRHS' loc (Constr mn con args)
    = let args' = map (toRHS' loc . snd) args in
          (mn, gapply (IVar loc con) args')

toRHS : FC -> Rec -> RawImp
toRHS fc r = snd (toRHS' fc r)

findConName : Defs -> Name -> Core (Maybe Name)
findConName defs tyn
    = case !(lookupDefExact tyn (gamma defs)) of
           Just (TCon _ _ _ _ _ (Just [con]) _) => pure (Just con)
           _ => pure Nothing

findFieldsAndTypeArgs : {auto c : Ref Ctxt Defs} ->
                        Defs -> Name ->
                        Core $ Maybe (List (String, Maybe Name, Maybe Name), SortedSet Name)
findFieldsAndTypeArgs defs con
    = case !(lookupTyExact con (gamma defs)) of
           Just t => pure (Just !(getExpNames empty [] !(nf defs Env.empty t)))
           _ => pure Nothing
  where
    getExpNames : SortedSet Name ->
                  List (String, Maybe Name, Maybe Name) ->
                  ClosedNF ->
                  Core (List (String, Maybe Name, Maybe Name), SortedSet Name)
    getExpNames names expNames (NBind fc x (Pi _ _ p ty) sc)
        = do let imp = case p of
                            Explicit => Nothing
                            _ => Just x
             nfty <- evalClosure defs ty
             let names = !(getNames defs nfty) `union` names
             let expNames = (nameRoot x, imp, getRecordType Env.empty nfty) :: expNames
             getExpNames names expNames !(sc defs (toClosure defaultOpts Env.empty (Ref fc Bound x)))
    getExpNames names expNames nfty = pure (reverse expNames, (!(getNames defs nfty) `union` names))

genFieldName : {auto u : Ref UST UState} ->
               String -> Core String
genFieldName root
    = do ust <- get UST
         put UST ({ nextName $= (+1) } ust)
         pure (root ++ show (nextName ust))

-- There's probably a generic version of this in the prelude isn't
-- there?
replace : String -> Rec ->
          List (String, Rec) -> List (String, Rec)
replace k v [] = []
replace k v ((k', v') :: vs)
    = if k == k'
         then ((k, v) :: vs)
         else ((k', v') :: replace k v vs)

findPath : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           FC -> List String -> List String -> Maybe Name ->
           (String -> RawImp) ->
           Rec -> Core Rec
findPath loc [] full tyn val (Field mn lhs _) = pure (Field mn lhs (val lhs))
findPath loc [] full tyn val rec
   = throw (IncompatibleFieldUpdate loc full)
findPath loc (p :: ps) full Nothing val (Field mn n v)
   = throw (NotRecordField loc p Nothing)
findPath loc (p :: ps) full (Just tyn) val (Field mn n v)
   = do defs <- get Ctxt
        Just con <- findConName defs tyn
             | Nothing => throw (NotRecordType loc tyn)
        Just (fs, tyArgs) <- findFieldsAndTypeArgs defs con
             | Nothing => throw (NotRecordType loc tyn)
        args <- mkArgs fs tyArgs
        let rec' = Constr mn con args
        findPath loc (p :: ps) full (Just tyn) val rec'
  where
    mkArgs : List (String, Maybe Name, Maybe Name) ->
             SortedSet Name ->
             Core (List (String, Rec))
    mkArgs [] _ = pure []
    mkArgs ((p, imp, _) :: ps) tyArgs
        = do fldn <- genFieldName p
             args' <- mkArgs ps tyArgs
             -- If other types depend on that implicit argument, leave it as _ by default
             let arg = case (flip contains tyArgs) <$> imp of
                  Just True => Implicit loc False
                  _ => IVar (virtualiseFC loc) (UN $ Basic fldn)
             pure ((p, Field imp fldn arg) :: args')

findPath loc (p :: ps) full tyn val (Constr mn con args)
   = do let Just prec = lookup p args
                 | Nothing => throw (NotRecordField loc p tyn)
        defs <- get Ctxt
        Just (fs, _) <- findFieldsAndTypeArgs defs con
             | Nothing => pure (Constr mn con args)
        let Just (imp, mfty) = lookup p fs
                 | Nothing => throw (NotRecordField loc p tyn)
        prec' <- findPath loc ps full mfty val prec
        pure (Constr mn con (replace p prec' args))

getSides : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           FC -> IFieldUpdate -> Name -> RawImp -> Rec ->
           Core Rec
getSides loc (ISetField path val) tyn orig rec
   -- update 'rec' so that 'path' is accessible on the lhs and rhs,
   -- then set the path on the rhs to 'val'
   = findPath loc path path (Just tyn) (const val) rec
getSides loc (ISetFieldApp path val) tyn orig rec
   = findPath loc path path (Just tyn)
      (\n => apply val [IVar (virtualiseFC loc) (UN $ Basic n)]) rec

getAllSides : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> List IFieldUpdate -> Name ->
              RawImp -> Rec ->
              Core Rec
getAllSides loc [] tyn orig rec = pure rec
getAllSides loc (u :: upds) tyn orig rec
    = getAllSides loc upds tyn orig !(getSides loc u tyn orig rec)

checkForDuplicates :
  List IFieldUpdate ->
  (seen, dups : SortedSet (List String)) ->
  SortedSet (List String)
checkForDuplicates [] seen dups = dups
checkForDuplicates (x :: xs) seen dups
  = let path = getFieldUpdatePath x
        dups = ifThenElse (contains path seen) (insert path dups) dups
    in checkForDuplicates xs (insert path seen) dups

-- Convert the collection of high level field accesses into a case expression
-- which does the updates all in one go
export
recUpdate : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            RigCount -> ElabInfo -> FC ->
            NestedNames vars -> Env Term vars ->
            List IFieldUpdate ->
            (rec : RawImp) -> (grecty : Glued vars) ->
            Core RawImp
recUpdate rigc elabinfo iloc nest env flds rec grecty
      = do let dups = checkForDuplicates flds empty empty
           unless (null dups) $
             throw (DuplicatedRecordUpdatePath iloc $ Prelude.toList dups)
           defs <- get Ctxt
           rectynf <- getNF grecty
           let Just rectyn = getRecordType env rectynf
                    | Nothing => throw (RecordTypeNeeded iloc env)
           fldn <- genFieldName "__fld"
           sides <- getAllSides iloc flds rectyn rec
                                (Field Nothing fldn (IVar vloc (UN $ Basic fldn)))
           pure $ ICase vloc [] rec (Implicit vloc False) [mkClause sides]
  where
    vloc : FC
    vloc = virtualiseFC iloc

    mkClause : Rec -> ImpClause
    mkClause rec = PatClause vloc (toLHS vloc rec) (toRHS vloc rec)

needType : Error -> Bool
needType (RecordTypeNeeded {}) = True
needType (InType _ _ err) = needType err
needType (InCon _ err) = needType err
needType (InLHS _ _ err) = needType err
needType (InRHS _ _ err) = needType err
needType (WhenUnifying _ _ _ _ _ err) = needType err
needType _ = False

export
checkUpdate : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto e : Ref EST (EState vars)} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
              RigCount -> ElabInfo ->
              NestedNames vars -> Env Term vars ->
              FC -> List IFieldUpdate -> RawImp -> Maybe (Glued vars) ->
              Core (Term vars, Glued vars)
checkUpdate rig elabinfo nest env fc upds rec expected
    = do recty <- case expected of
                       Just ret => pure ret
                       _ => do (_, ty) <- checkImp rig elabinfo
                                                   nest env rec Nothing
                               pure ty
         let solvemode = case elabMode elabinfo of
                              InLHS c => inLHS
                              _ => inTerm
         delayOnFailure fc rig env (Just recty) needType RecordUpdate $
           \delayed =>
             do solveConstraints solvemode Normal
                exp <- getTerm recty
                -- We can't just use the old NF on the second attempt,
                -- because we might know more now, so recalculate it
                let recty' = if delayed
                                then gnf env exp
                                else recty
                logGlueNF "elab.record" 5 (show delayed ++ " record type " ++ show rec) env recty'
                rcase <- recUpdate rig elabinfo fc nest env upds rec recty'
                log "elab.record" 5 $ "Record update: " ++ show rcase
                check rig elabinfo nest env rcase expected
