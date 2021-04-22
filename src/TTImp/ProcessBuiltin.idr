||| Checking a %builtin pragma is correct.
-- If we get more builtins it might be wise to move each builtin to it's own file.
module TTImp.ProcessBuiltin

import Libraries.Data.Bool.Extra
import Libraries.Data.NameMap
import Data.List

import Core.Core
import Core.Context
import Core.Context.Log
import Core.Env
import Core.Metadata
import Core.TT
import Core.UnifyState

import TTImp.TTImp

||| Get the return type.
getRetTy : {vars : _} -> Term vars -> Maybe (vars ** Term vars)
getRetTy tm@(Bind _ x b scope) = case b of
    Lam _ _ _ _ => Nothing
    Let _ _ val _ => getRetTy $ subst {x} val scope
    Pi _ _ _ _ => getRetTy scope
    _ => Nothing
getRetTy tm = Just (vars ** tm)

||| Get the first non-erased argument type.
getFirstNETy : {vars : _} -> Term vars -> Maybe (vars ** Term vars)
getFirstNETy (Bind _ x b tm) = case b of
    Let _ _ val _ => getFirstNETy $ subst {x} val tm
    Pi _ mul _ arg => if isErased mul
        then getFirstNETy tm
        else Just (_ ** arg)
    _ => Nothing
getFirstNETy tm = Nothing

||| Do the terms match ignoring arguments to type constructors.
termConMatch : Term vs -> Term vs' -> Bool
termConMatch (Local _ _ x _) (Local _ _ y _) = x == y
termConMatch (Ref _ _ n) (Ref _ _ m) = n == m
termConMatch (Meta _ _ i args0) (Meta _ _ j args1)
    = i == j && allTrue (zipWith termConMatch args0 args1)
    -- I don't understand how they're equal if args are different lengths
    -- but this is what's in Core.TT.
termConMatch (Bind _ _ b s) (Bind _ _ c t) = eqBinderBy termConMatch b c && termConMatch s t
termConMatch (App _ f _) (App _ g _) = termConMatch f g
termConMatch (As _ _ a p) (As _ _ b q) = termConMatch a b && termConMatch p q
termConMatch (TDelayed _ _ tm0) tm1 = termConMatch tm0 tm1
termConMatch tm0 (TDelayed _ _ tm1) = termConMatch tm0 tm1
    -- don't check for laziness here to give more accurate error messages.
termConMatch (TDelay _ _ tm0 x0) (TDelay _ _ tm1 x1) = termConMatch tm0 tm1 && termConMatch x0 x1
termConMatch (TForce _ _ tm0) tm1 = termConMatch tm0 tm1
termConMatch tm0 (TForce _ _ tm1) = termConMatch tm0 tm1
termConMatch (PrimVal _ _) (PrimVal _ _) = True -- no constructor to check.
termConMatch (Erased _ _) (Erased _ _) = True -- return type can't erased?
termConMatch (TType _) (TType _) = True
termConMatch _ _ = False

||| Check a type is strict.
isStrict : Term vs -> Bool
isStrict (Local _ _ _ _) = True
isStrict (Ref _ _ _) = True
isStrict (Meta _ _ i args) = all isStrict args
isStrict (Bind _ _ b s) = isStrict (binderType b) && isStrict s
isStrict (App _ f x) = isStrict f && isStrict x
isStrict (As _ _ a p) = isStrict a && isStrict p
isStrict (TDelayed _ _ _) = False
isStrict (TDelay _ _ f x) = isStrict f && isStrict x
isStrict (TForce _ _ tm) = isStrict tm
isStrict (PrimVal _ _) = True
isStrict (Erased _ _) = True
isStrict (TType _) = True

||| Get the name and arity (of non-erased arguments only) of a list of names.
||| `cons` should all be data constructors (`DCon`) otherwise it will throw an error.
getConsGDef : Context -> FC -> (cons : List Name) -> Core $ List (Name, GlobalDef)
getConsGDef c fc = traverse \n => do
    [(n', _, gdef)] <- lookupCtxtName n c
        | [] => throw $ UndefinedName fc n
        | ns => throw $ AmbiguousName fc $ (\(n, _, _) => n) <$> ns
    pure (n', gdef)

||| Check a list of constructors has exactly
||| 1 'Z'-like constructor
||| and 1 `S`-like constructor, which has type `ty -> ty` or `ty arg -> `ty (f arg)`.
checkCons : Context -> (cons : List (Name, GlobalDef)) -> (dataType : Name) -> FC -> Core NatBuiltin
checkCons c cons ty fc = case !(foldr checkCon (pure (Nothing, Nothing)) cons) of
    (Just zero, Just succ) => pure $ MkNatBuiltin {zero, succ}
    (Nothing, _) => throw $ GenericMsg fc $ "No 'Z'-like constructors for " ++ show ty ++ "."
    (_, Nothing) => throw $ GenericMsg fc $ "No 'S'-like constructors for " ++ show ty ++ "."
  where
    ||| Check if a list of names contains a name.
    checkSArgType : List Name -> Core ()
    checkSArgType [] = throw $ GenericMsg fc $ "'S'-like constructor for " ++ show ty ++ " is missing argument of type: " ++ show ty
    checkSArgType (n :: ns) = if nameRoot n == nameRoot ty && (n `matches` ty)
        then checkSArgType ns
        else throw $ GenericMsg fc $ "'S'-like constructor for " ++ show ty ++ " has unexpected argument: " ++ show n

    ||| Check the type of an 'S'-like constructor.
    checkTyS : Name -> GlobalDef -> Core ()
    checkTyS n gdef = do
        let type = gdef.type
            erase = gdef.eraseArgs
        let Just (_ ** arg) = getFirstNETy type
            | Nothing => throw $ InternalError "Expected a non-erased argument, found none."
        let Just (_ ** ret) = getRetTy type
            | Nothing => throw $ InternalError $ "Unexpected type " ++ show type
        unless (termConMatch arg ret) $ throw $ GenericMsg fc $ "Incorrect type for 'S'-like constructor for " ++ show ty ++ "."
        unless (isStrict arg) $ throw $ GenericMsg fc $ "Natural builtin does not support lazy types, as they can be potentially infinite."
        pure ()

    ||| Check a constructor's arity and type.
    -- 'Z'-like constructor is always first, then 'S'-like constructor.
    checkCon : (Name, GlobalDef) -> Core (Maybe Name, Maybe Name) -> Core (Maybe Name, Maybe Name)
    checkCon (n, gdef) cons = do
        (zero, succ) <- cons
        let DCon _ arity _ = gdef.definition
            | def => throw $ GenericMsg fc $ "Expected data constructor, found:\n" ++ show def
        case arity `minus` length gdef.eraseArgs of
            0 => case zero of
                Just _ => throw $ GenericMsg fc $ "Multiple 'Z'-like constructors for " ++ show ty ++ "."
                Nothing => pure (Just n, succ)
            1 => case succ of
                Just _ => throw $ GenericMsg fc $ "Multiple 'S'-like constructors for " ++ show ty ++ "."
                Nothing => do
                    checkTyS n gdef
                    pure (zero, Just n)
            _ => throw $ GenericMsg fc $ "Constructor " ++ show n ++ " doesn't match any pattern for Natural."

addBuiltinNat :
    {auto c : Ref Ctxt Defs} ->
    (ty : Name) -> NatBuiltin -> Core ()
addBuiltinNat type cons = do
    log "builtin.Natural.addTransform" 10 $ "Add Builtin Natural transform for " ++ show type
    update Ctxt $ record
        { builtinTransforms.natTyNames $= insert type cons
        , builtinTransforms.natZNames $= insert cons.zero MkZERO
        , builtinTransforms.natSNames $= insert cons.succ MkSUCC
        }

||| Check a `%builtin Natural` pragma is correct.
processBuiltinNatural :
    {auto c : Ref Ctxt Defs} ->
    {auto m : Ref MD Metadata} ->
    {auto u : Ref UST UState} ->
    Defs -> FC -> Name -> Core ()
processBuiltinNatural ds fc name = do
    log "builtin.Natural" 5 $ "Processing Builtin Natural pragma for " ++ show name
    [(n, _, gdef)] <- lookupCtxtName name ds.gamma
        | [] => throw $ UndefinedName fc name
        | ns => throw $ AmbiguousName fc $ (\(n, _, _) => n) <$> ns
    let TCon _ _ _ _ _ _ dcons _ = gdef.definition
        | def => throw $ GenericMsg fc $ "Expected a type constructor, found:\n" ++ show def
    cons <- getConsGDef ds.gamma fc dcons
    cons <- checkCons ds.gamma cons n fc
    zero <- getFullName cons.zero
    succ <- getFullName cons.succ
    n <- getFullName name
    addBuiltinNat n $ MkNatBuiltin {zero, succ}

||| Check a `%builtin` pragma is correct.
export
processBuiltin :
    {auto c : Ref Ctxt Defs} ->
    {auto m : Ref MD Metadata} ->
    {auto u : Ref UST UState} ->
    NestedNames vars -> Env Term vars -> FC -> BuiltinType -> Name -> Core ()
processBuiltin nest env fc type name = do
    ds <- get Ctxt
    case type of
        BuiltinNatural => processBuiltinNatural ds fc name
        _ => throw $ InternalError $ "%builtin " ++ show type ++ " not yet implemented."
