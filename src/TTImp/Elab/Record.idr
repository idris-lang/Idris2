module TTImp.Elab.Record

import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.TTImp

import Data.List

%default covering

getRecordType : Env Term vars -> NF vars -> Maybe Name
getRecordType env (NTCon _ n _ _ _) = Just n
getRecordType env _ = Nothing

data Rec : Type where
     Field : String -> RawImp -> Rec -- field name on left, value on right
     Constr : Name -> List (String, Rec) -> Rec

toLHS : FC -> Rec -> RawImp
toLHS loc (Field n _) = IBindVar loc n
toLHS loc (Constr con args)
    = let args' = map (\a => toLHS loc (snd a)) args in
          apply (IVar loc con) args'

toRHS : FC -> Rec -> RawImp
toRHS loc (Field _ val) = val
toRHS loc (Constr con args)
    = let args' = map (\a => toRHS loc (snd a)) args in
          apply (IVar loc con) args'

findConName : Defs -> Name -> Core (Maybe Name)
findConName defs tyn
    = case !(lookupDefExact tyn (gamma defs)) of
           Just (TCon _ _ _ _ _ _ [con] _) => pure (Just con)
           _ => pure Nothing

findFields : Defs -> Name -> Core (Maybe (List (String, Maybe Name)))
findFields defs con
    = case !(lookupTyExact con (gamma defs)) of
           Just t => pure (Just !(getExpNames !(nf defs [] t)))
           _ => pure Nothing
  where
    getExpNames : NF [] -> Core (List (String, Maybe Name))
    getExpNames (NBind fc x (Pi _ p ty) sc)
        = do rest <- getExpNames !(sc defs (toClosure defaultOpts [] (Erased fc False)))
             case p of
                  Explicit => pure $ (nameRoot x, getRecordType [] ty) :: rest
                  _ => pure rest
    getExpNames _ = pure []

genFieldName : {auto u : Ref UST UState} ->
               String -> Core String
genFieldName root
    = do ust <- get UST
         put UST (record { nextName $= (+1) } ust)
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
findPath loc [] full tyn val (Field lhs _) = pure (Field lhs (val lhs))
findPath loc [] full tyn val rec
   = throw (IncompatibleFieldUpdate loc full)
findPath loc (p :: ps) full Nothing val (Field n v)
   = throw (NotRecordField loc p Nothing)
findPath loc (p :: ps) full (Just tyn) val (Field n v)
   = do defs <- get Ctxt
        Just con <- findConName defs tyn
             | Nothing => throw (NotRecordType loc tyn)
        Just fs <- findFields defs con
             | Nothing => throw (NotRecordType loc tyn)
        args <- mkArgs fs
        let rec' = Constr con args
        findPath loc (p :: ps) full (Just tyn) val rec'
  where
    mkArgs : List (String, Maybe Name) ->
             Core (List (String, Rec))
    mkArgs [] = pure []
    mkArgs ((p, _) :: ps)
        = do fldn <- genFieldName p
             args' <- mkArgs ps
             pure ((p, Field fldn (IVar loc (UN fldn))) :: args')

findPath loc (p :: ps) full tyn val (Constr con args)
   = do let Just prec = lookup p args
                 | Nothing => throw (NotRecordField loc p tyn)
        defs <- get Ctxt
        Just fs <- findFields defs con
             | Nothing => pure (Constr con args)
        let Just mfty = lookup p fs
                 | Nothing => throw (NotRecordField loc p tyn)
        prec' <- findPath loc ps full mfty val prec
        pure (Constr con (replace p prec' args))

getSides : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           FC -> IFieldUpdate -> Name -> RawImp -> Rec ->
           Core Rec
getSides loc (ISetField path val) tyn orig rec
   -- update 'rec' so that 'path' is accessible on the lhs and rhs,
   -- then set the path on the rhs to 'val'
   = findPath loc path path (Just tyn) (const val) rec
getSides loc (ISetFieldApp path val) tyn orig rec
   = findPath loc path path (Just tyn) (\n => apply val [IVar loc (UN n)]) rec
 where
   get : List String -> RawImp -> RawImp
   get [] rec = rec
   get (p :: ps) rec = get ps (IApp loc (IVar loc (UN p)) rec)

getAllSides : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> List IFieldUpdate -> Name ->
              RawImp -> Rec ->
              Core Rec
getAllSides loc [] tyn orig rec = pure rec
getAllSides loc (u :: upds) tyn orig rec
    = getAllSides loc upds tyn orig !(getSides loc u tyn orig rec)

-- Convert the collection of high level field accesses into a case expression
-- which does the updates all in one go
export
recUpdate : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            RigCount -> ElabInfo -> FC ->
            NestedNames vars -> Env Term vars ->
            List IFieldUpdate ->
            (rec : RawImp) -> (grecty : Glued vars) ->
            Core RawImp
recUpdate rigc elabinfo loc nest env flds rec grecty
      = do defs <- get Ctxt
           rectynf <- getNF grecty
           let Just rectyn = getRecordType env rectynf
                    | Nothing => throw (RecordTypeNeeded loc env)
           fldn <- genFieldName "__fld"
           sides <- getAllSides loc flds rectyn rec (Field fldn (IVar loc (UN fldn)))
           pure $ ICase loc rec (Implicit loc False) [mkClause sides]
  where
    mkClause : Rec -> ImpClause
    mkClause rec = PatClause loc (toLHS loc rec) (toRHS loc rec)

needType : Error -> Bool
needType (RecordTypeNeeded _ _) = True
needType (InType _ _ err) = needType err
needType (InCon _ _ err) = needType err
needType (InLHS _ _ err) = needType err
needType (InRHS _ _ err) = needType err
needType (WhenUnifying _ _ _ _ err) = needType err
needType _ = False

export
checkUpdate : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto e : Ref EST (EState vars)} ->
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
                              _ => inTermP False
         delayOnFailure fc rig env recty needType 5 $
           \delayed =>
             do solveConstraints solvemode Normal
                exp <- getTerm recty
                -- We can't just use the old NF on the second attempt,
                -- because we might know more now, so recalculate it
                let recty' = if delayed
                                then gnf env exp
                                else recty
                logGlueNF 5 (show delayed ++ " record type " ++ show rec) env recty'
                rcase <- recUpdate rig elabinfo fc nest env upds rec recty'
                log 5 $ "Record update: " ++ show rcase
                check rig elabinfo nest env rcase expected
