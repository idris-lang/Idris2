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
getConsArity : Context -> FC -> (cons : List Name) -> Core $ List (Name, Nat)
getConsArity c fc = traverse \n => do
    [(n', _, gdef)] <- lookupCtxtName n c
        | [] => throw $ UndefinedName fc n
        | ns => throw $ AmbiguousName fc $ (\(n, _, _) => n) <$> ns
    let (DCon _ a _) = gdef.definition
        | def => throw $ GenericMsg fc $ "Expected a data constructor, found:\n" ++ show def
    pure (n', a `minus` length gdef.eraseArgs)

||| Check a list of constructors has exactly
||| 1 'Z'-like constructor
||| and 1 `S`-like constructor.
checkCons : (cons : List (Name, Nat)) -> (type : Name) -> FC -> Core ()
checkCons cons ty fc = case !(foldr checkCon (pure (False, False)) cons) of
    (True, True) => pure ()
    (False, _) => throw $ GenericMsg fc $ "No 'Z'-like constructors for " ++ show ty ++ "."
    (_, False) => throw $ GenericMsg fc $ "No 'S'-like constructors for " ++ show ty ++ "."
  where
    checkCon : (Name, Nat) -> Core (Bool, Bool) -> Core (Bool, Bool)
    checkCon (n, arity) has = do
        (hasZ, hasS) <- has
        case arity of
            0 => case hasZ of
                True => throw $ GenericMsg fc $ "Multiple 'Z'-like constructors for " ++ show ty ++ "."
                False => pure (True, hasS)
            1 => case hasS of
                True => throw $ GenericMsg fc $ "Multiple 'S'-like constructors for " ++ show ty ++ "."
                False => pure (hasZ, True)
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
    cons <- getConsArity ds.gamma fc dcons
    checkCons cons n fc

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