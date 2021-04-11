||| Checking a %builtin pragma is correct.
-- If we get more builtins it might be wise to move each builtin to it's own file.
module TTImp.ProcessBuiltin

import Libraries.Data.Bool.Extra
import Data.List

import Core.Core
import Core.Context
import Core.Env
import Core.Metadata
import Core.TT
import Core.UnifyState

import TTImp.TTImp

||| Get the return type.
getRetTy : {vars : _} -> Term vars -> (vars ** Term vars)
getRetTy (Bind _ _ _ tm) = getRetTy tm
getRetTy tm = (vars ** tm)

||| Get the first non-erased argument type.
getFirstNETy : {vars : _} -> Term vars -> (vars ** Term vars)
getFirstNETy (Bind _ _ b tm) = if isErased $ multiplicity b
    then getFirstNETy tm
    else (_ ** binderType b)
getFirstNETy tm = (vars ** tm)

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
checkCons : Context -> (cons : List (Name, GlobalDef)) -> (dataType : Name) -> FC -> Core ()
checkCons c cons ty fc = case !(foldr checkCon (pure (False, False)) cons) of
    (True, True) => pure ()
    (False, _) => throw $ GenericMsg fc $ "No 'Z'-like constructors for " ++ show ty ++ "."
    (_, False) => throw $ GenericMsg fc $ "No 'S'-like constructors for " ++ show ty ++ "."
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
        let (_ ** arg) = getFirstNETy type
        let (_ ** ret) = getRetTy type
        unless (termConMatch arg ret) $ throw $ GenericMsg fc $ "Incorrect type for 'S'-like constructor for " ++ show ty ++ "."
        unless (isStrict arg) $ throw $ GenericMsg fc $ "Natural builtin does not support lazy types, as they can be potentially infinite."
        pure ()

    ||| Check a constructor's arity and type.
    checkCon : (Name, GlobalDef) -> Core (Bool, Bool) -> Core (Bool, Bool)
    checkCon (n, gdef) has = do
        (hasZ, hasS) <- has
        let DCon _ arity _ = gdef.definition
            | def => throw $ GenericMsg fc $ "Expected data constructor, found:\n" ++ show def
        case arity `minus` length gdef.eraseArgs of
            0 => case hasZ of
                True => throw $ GenericMsg fc $ "Multiple 'Z'-like constructors for " ++ show ty ++ "."
                False => pure (True, hasS)
            1 => case hasS of
                True => throw $ GenericMsg fc $ "Multiple 'S'-like constructors for " ++ show ty ++ "."
                False => do
                    checkTyS n gdef
                    pure (hasZ, True)
            _ => throw $ GenericMsg fc $ "Constructor " ++ show n ++ " doesn't match any pattern for Natural."


||| Check a `%builtin Natural _` pragma is correct.
processBuiltinNatural :
    {auto c : Ref Ctxt Defs} ->
    {auto m : Ref MD Metadata} ->
    {auto u : Ref UST UState} ->
    Defs -> NestedNames vars -> Env Term vars -> FC -> Name -> Core ()
processBuiltinNatural ds nest env fc name = do
    [(n, _, gdef)] <- lookupCtxtName name ds.gamma
        | [] => throw $ UndefinedName fc name
        | ns => throw $ AmbiguousName fc $ (\(n, _, _) => n) <$> ns
    let TCon _ _ _ _ _ _ dcons _ = gdef.definition
        | def => throw $ GenericMsg fc $ "Expected a type constructor, found:\n" ++ show def
    cons <- getConsGDef ds.gamma fc dcons
    checkCons ds.gamma cons n fc

||| Check a `%builtin _ _` pragma is correct.
export
processBuiltin :
    {auto c : Ref Ctxt Defs} ->
    {auto m : Ref MD Metadata} ->
    {auto u : Ref UST UState} ->
    NestedNames vars -> Env Term vars -> FC -> BuiltinType -> Name -> Core ()
processBuiltin nest env fc type name = do
    ds <- get Ctxt
    case type of
        BuiltinNatural => processBuiltinNatural ds nest env fc name
