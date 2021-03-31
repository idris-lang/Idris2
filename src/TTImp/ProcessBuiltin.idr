||| Checking a %builtin pragma is correct.
-- If we get more builtins it might be wise to move each builtin to it's own file.
module TTImp.ProcessBuiltin

import Core.Core
import Core.Context
import Core.Env
import Core.Metadata
import Core.TT
import Core.UnifyState

import TTImp.TTImp

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
||| and 1 `S`-like constructor
||| and if the types are correct.
checkCons : Context -> (cons : List (Name, GlobalDef)) -> (dataType : Name) -> FC -> Core ()
checkCons c cons ty fc = case !(foldr checkCon (pure (False, False)) cons) of
    (True, True) => pure ()
    (False, _) => throw $ GenericMsg fc $ "No 'Z'-like constructors for " ++ show ty ++ "."
    (_, False) => throw $ GenericMsg fc $ "No 'S'-like constructors for " ++ show ty ++ "."
  where
    ||| Check the type of an 'S'-like constructor.
    checkTyS : Name -> GlobalDef -> Core ()
    checkTyS n gdef = case gdef.type of
        _ => pure ()
    ||| Check the type of a 'Z'-like constructor.
    checkTyZ : Name -> GlobalDef -> Core ()
    checkTyZ n gdef = case gdef.type of
        _ => pure ()
    ||| Check a constructor's arity and type.
    checkCon : (Name, GlobalDef) -> Core (Bool, Bool) -> Core (Bool, Bool)
    checkCon (n, gdef) has = do
        (hasZ, hasS) <- has
        let DCon _ arity _ = gdef.definition
            | def => throw $ GenericMsg fc $ "Expected data constructor, found:\n" ++ show def
        case arity `minus` length gdef.eraseArgs of
            0 => case hasZ of
                True => throw $ GenericMsg fc $ "Multiple 'Z'-like constructors for " ++ show ty ++ "."
                False => checkTyZ n gdef *> pure (True, hasS)
            1 => case hasS of
                True => throw $ GenericMsg fc $ "Multiple 'S'-like constructors for " ++ show ty ++ "."
                False => checkTyS n gdef *> pure (hasZ, True)
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