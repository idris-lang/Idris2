||| Checking a %builtin pragma is correct.
-- If we get more builtins it might be wise to move each builtin to its own file.
module TTImp.ProcessBuiltin

import Data.List
import Libraries.Data.NatSet

import Core.Core
import Core.Context
import Core.Context.Log
import Core.CompileExpr
import Core.Env
import Core.TT

import TTImp.TTImp

%default covering

showDefType : Def -> String
showDefType None = "undefined"
showDefType (PMDef {}) = "function"
showDefType (ExternDef {}) = "external function"
showDefType (ForeignDef {}) = "foreign function"
showDefType (Builtin {}) = "builtin function"
showDefType (DCon {}) = "data constructor"
showDefType (TCon {}) = "type constructor"
showDefType (Hole {}) = "hole"
showDefType (BySearch {}) = "search"
showDefType (Guess {}) = "guess"
showDefType ImpBind = "bound name"
showDefType (UniverseLevel {}) = "universe level"
showDefType Delayed = "delayed"

||| Get the return type.
getReturnType : {vars : _} -> Term vars -> Maybe (vars ** Term vars)
getReturnType tm@(Bind _ x b scope) = case b of
    Let _ _ val _ => getReturnType $ subst {x} val scope
    Pi {} => getReturnType scope
    _ => Nothing
getReturnType tm = Just (vars ** tm)

||| Get the top level type constructor if there is one.
getTypeCons : {vars : _} -> Term vars -> Maybe Name
getTypeCons (Local _ _ _ p) = Just $ nameAt p
getTypeCons (Ref _ _ name) = Just name
getTypeCons (Meta {}) = Nothing
getTypeCons (Bind _ x b scope) = case b of
    Let _ _ val _ => getTypeCons $ subst {x} val scope
    _ => Nothing
getTypeCons (App _ fn _) = getTypeCons fn
getTypeCons _ = Nothing

||| Get the arguments of a `Term` representing a type.
getTypeArgs : {vars : _} -> Term vars -> List (vars ** Term vars)
getTypeArgs (Bind _ x b tm) = case b of
    Let _ _ val _ => getTypeArgs $ subst {x} val tm
    Pi _ _ _ arg => (_ ** arg) :: getTypeArgs tm
    _ => []
getTypeArgs _ = []

||| Get all non-erased aruments.
getNEArgs : {vars : _} -> Term vars -> List (vars ** Term vars)
getNEArgs (Bind _ x b tm) = case b of
    Let _ _ val _ => getNEArgs $ subst {x} val tm
    Pi _ mul _ arg => if isErased mul
        then getNEArgs tm
        else (_ ** arg) :: getNEArgs tm
    _ => []
getNEArgs _ = []

||| Get the first non-erased argument type.
getFirstNEType : {vars : _} -> Term vars -> Maybe (vars ** Term vars)
getFirstNEType tm = case getNEArgs tm of
    [] => Nothing
    arg :: _ => Just arg

||| Get the index of the first non-erased argument if it exists.
getNEIndex : Term vars -> Maybe Nat
getNEIndex (Bind _ x b tm) = case b of
    Let _ _ val _ => getNEIndex $ subst {x} val tm
    Pi _ mul _ arg => if isErased mul
        then getNEIndex tm
        else Just 0
    _ => Nothing
getNEIndex _ = Nothing

||| Get the index of all non-erased Integer argument.
getNEIntegerIndex : Term vars -> Maybe (List Nat)
getNEIntegerIndex (Bind _ x b tm) = case b of
    Let _ _ val _ => getNEIntegerIndex $ subst {x} val tm
    Pi _ mul _ arg => if not (isErased mul) && isInteger arg
        then Prelude.(::) 0 . map (+ 1) <$> getNEIntegerIndex tm
        else getNEIntegerIndex tm
    _ => Nothing
  where
    isInteger : forall vars. Term vars -> Bool
    isInteger (PrimVal _ $ PrT IntegerType) = True
    isInteger _ = False
getNEIntegerIndex _ = Just []

||| Do the terms match ignoring arguments to type constructors.
termConMatch : Term vs -> Term vs' -> Bool
termConMatch (Local _ _ x _) (Local _ _ y _) = x == y
termConMatch (Ref _ _ n) (Ref _ _ m) = n == m
termConMatch (Meta _ _ i args0) (Meta _ _ j args1)
    = i == j && all (uncurry termConMatch) (zip args0 args1)
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
termConMatch (PrimVal {}) (PrimVal {}) = True -- no constructor to check.
termConMatch (Erased {}) (Erased {}) = True -- return type can't erased?
termConMatch (TType {}) (TType {}) = True
termConMatch _ _ = False

||| Check a type is strict.
isStrict : Term vs -> Bool
isStrict (Local {}) = True
isStrict (Ref {}) = True
isStrict (Meta _ _ i args) = all isStrict args
isStrict (Bind _ _ b s) = isStrict (binderType b) && isStrict s
isStrict (App _ f x) = isStrict f && isStrict x
isStrict (As _ _ a p) = isStrict a && isStrict p
isStrict (TDelayed {}) = False
isStrict (TDelay _ _ f x) = isStrict f && isStrict x
isStrict (TForce _ _ tm) = isStrict tm
isStrict (PrimVal {}) = True
isStrict (Erased {}) = True
isStrict (TType {}) = True

||| Get the name and definition of a list of names.
getConsGDef :
    Ref Ctxt Defs =>
    FC -> (cons : List Name) ->
    Core $ List (Name, GlobalDef)
getConsGDef fc cons = do
    defs <- get Ctxt
    let c = defs.gamma
    for cons $ \n => do
        [(n', _, gdef)] <- lookupCtxtName n c
            | ns => ambiguousName fc n $ (\(n, _, _) => n) <$> ns
        pure (n', gdef)

isNatural : Ref Ctxt Defs => FC ->Name -> Core Bool
isNatural fc n = do
    defs <- get Ctxt
    Just gdef <- lookupCtxtExact n defs.gamma
        | Nothing => undefinedName EmptyFC n
    let TCon _ _ _ _ _ cons _ = gdef.definition
        | _ => pure False
    consDefs <- getConsGDef fc (fromMaybe [] cons)
    pure $ all hasNatFlag consDefs
  where
    isNatFlag : DefFlag -> Bool
    isNatFlag (ConType ZERO) = True
    isNatFlag (ConType SUCC) = True
    isNatFlag _ = False
    hasNatFlag : (Name, GlobalDef) -> Bool
    hasNatFlag (_, gdef) = any isNatFlag gdef.flags

||| Check a list of constructors has exactly
||| 1 'Z'-like constructor
||| and 1 `S`-like constructor, which has type `ty -> ty` or `ty arg -> `ty (f arg)`.
checkNatCons : Context -> (cons : List (Name, GlobalDef)) -> (dataType : Name) -> FC -> Core ()
checkNatCons c cons ty fc = case !(foldr checkCon (pure (Nothing, Nothing)) cons) of
    (Just zero, Just succ) => pure ()
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
        let Just (_ ** arg) = getFirstNEType type
            | Nothing => throw $ InternalError "Expected a non-erased argument, found none."
        let Just (_ ** ret) = getReturnType type
            | Nothing => throw $ InternalError $ "Unexpected type " ++ show type
        unless (termConMatch arg ret) $ throw $ GenericMsg fc $ "Incorrect type for 'S'-like constructor for " ++ show ty ++ "."
        unless (isStrict arg) $ throw $ GenericMsg fc $ "Natural builtin does not support lazy types."
        pure ()

    ||| Check a constructor's arity and type.
    -- 'Z'-like constructor is always first, then 'S'-like constructor.
    checkCon : (Name, GlobalDef) -> Core (Maybe Name, Maybe Name) -> Core (Maybe Name, Maybe Name)
    checkCon (n, gdef) cons = do
        (zero, succ) <- cons
        let DCon _ arity _ = gdef.definition
            | def => throw $ GenericMsg fc $ "Expected data constructor, found:" ++ showDefType def
        case arity `minus` size gdef.eraseArgs of
            0 => case zero of
                Just _ => throw $ GenericMsg fc $ "Multiple 'Z'-like constructors for " ++ show ty ++ "."
                Nothing => pure (Just n, succ)
            1 => case succ of
                Just _ => throw $ GenericMsg fc $ "Multiple 'S'-like constructors for " ++ show ty ++ "."
                Nothing => do
                    checkTyS n gdef
                    pure (zero, Just n)
            _ => throw $ GenericMsg fc $ "Constructor " ++ show n ++ " doesn't match any pattern for Natural."

||| Check a `%builtin Natural` pragma is correct.
processBuiltinNatural :
    Ref Ctxt Defs =>
    FC -> Name -> Core ()
processBuiltinNatural fc name = do
    ds <- get Ctxt
    log "builtin.Natural" 5 $ "Processing %builtin Natural " ++ show name ++ "."
    [(n, _, gdef)] <- lookupCtxtName name ds.gamma
        | ns => ambiguousName fc name $ (\(n, _, _) => n) <$> ns
    False <- isNatural fc n
        | True => pure ()
    let TCon _ _ _ _ _ dcons _ = gdef.definition
        | def => throw $ GenericMsg fc
            $ "Expected a type constructor, found " ++ showDefType def ++ "."
    cons <- getConsGDef fc (fromMaybe [] dcons)
    checkNatCons ds.gamma cons n fc

||| Check a `%builtin NaturalToInteger` pragma is correct.
processNatToInteger :
    Ref Ctxt Defs =>
    FC -> Name -> Core ()
processNatToInteger fc fn = do
    let show_fn = show fn
    ds <- get Ctxt
    log "builtin.NaturalToInteger" 5 $ "Processing %builtin NaturalToInteger " ++ show_fn ++ "."
    [(_ , i, gdef)] <- lookupCtxtName fn ds.gamma
        | ns => ambiguousName fc fn $ (\(n, _, _) => n) <$> ns
    let PMDef _ args _ cases _ = gdef.definition
        | def => throw $ GenericMsg fc
            $ "Expected function definition, found " ++ showDefType def ++ "."
    type <- toFullNames gdef.type
    logTerm "builtin.NaturalToInteger" 25 ("Type of " ++ show_fn) type
    let [(_ ** arg)] = getNEArgs type
        | [] => throw $ GenericMsg fc $ "No arguments found for " ++ show_fn ++ "."
        | _ => throw $ GenericMsg fc $ "More than 1 non-erased arguments found for " ++ show_fn ++ "."
    let Just tyCon = getTypeCons arg
        | Nothing => throw $ GenericMsg fc
            $ "No type constructor found for non-erased arguement of " ++ show_fn ++ "."
    True <- isNatural fc tyCon
        | False => throw $ GenericMsg fc $ "Non-erased argument is not a 'Nat'-like type."
    let Just natIdx = getNEIndex type
        | Nothing => throw $ InternalError "Couldn't find non-erased argument."
    setFlag fc (Resolved i) $ Identity natIdx

||| Check a `%builtin IntegerToNatural` pragma is correct.
processIntegerToNat :
    Ref Ctxt Defs =>
    FC -> Name -> Core ()
processIntegerToNat fc fn = do
    let show_fn = show fn
    ds <- get Ctxt
    log "builtin.IntegerToNatural" 5 $ "Processing %builtin IntegerToNatural " ++ show_fn ++ "."
    [(_, i, gdef)] <- lookupCtxtName fn ds.gamma
        | ns => ambiguousName fc fn $ (\(n, _, _) => n) <$> ns
    type <- toFullNames gdef.type
    let PMDef _ _ _ _ _ = gdef.definition
        | def => throw $ GenericMsg fc
            $ "Expected function definition, found " ++ showDefType def ++ "."
    logTerm "builtin.IntegerToNatural" 25 ("Type of " ++ show_fn) type
    let Just [intIdx] = getNEIntegerIndex type
        | Just [] => throw $ GenericMsg fc $ "No unrestricted arguments of type `Integer` found for " ++ show_fn ++ "."
        | Just _ => throw $ GenericMsg fc $ "More than one unrestricted arguments of type `Integer` found for " ++ show_fn ++ "."
        | Nothing => throw $ InternalError
            $ "Unexpected arity while processing %builtin IntegerToNatural " ++ show_fn ++ " (getNEIntegerIndex returned Nothing)"
    let Just (_ ** retTy) = getReturnType type
        | Nothing => throw $ InternalError $ "Unexpected type " ++ show type
    let Just retCon = getTypeCons retTy
        | Nothing => throw $ GenericMsg fc
            $ "No type constructor found for return type of " ++ show_fn ++ "."
    True <- isNatural fc retCon
        | False => throw $ GenericMsg fc $ "Return type is not a 'Nat'-like type"
    setFlag fc (Resolved i) $ Identity intIdx

||| Check a `%builtin` pragma is correct.
export
processBuiltin :
    Ref Ctxt Defs =>
    NestedNames vars -> Env Term vars -> FC -> BuiltinType -> Name -> Core ()
processBuiltin nest env fc type name = do
    case type of
        BuiltinNatural => processBuiltinNatural fc name
        NaturalToInteger => processNatToInteger fc name
        IntegerToNatural => processIntegerToNat fc name
