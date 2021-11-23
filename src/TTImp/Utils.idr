module TTImp.Utils

import Core.Context
import Core.Options
import Core.TT
import TTImp.TTImp

import Data.List
import Data.List1
import Data.String

import Idris.Syntax

import Libraries.Utils.String

%default covering


-- Appends the ' character to "x" until it is unique with respect to "xs".
export
genUniqueStr : (xs : List String) -> (x : String) -> String
genUniqueStr xs x = if x `elem` xs then genUniqueStr xs (x ++ "'") else x


-- Extract the RawImp pieces from a ImpDecl so they can be searched for unquotes
-- Used in findBindableNames{,Quot}
rawImpFromDecl : ImpDecl -> List RawImp
rawImpFromDecl decl = case decl of
    IClaim fc1 y z ys ty => [getFromTy ty]
    IData fc1 y (MkImpData fc2 n tycon opts datacons)
        => tycon :: map getFromTy datacons
    IData fc1 y (MkImpLater fc2 n tycon) => [tycon]
    IDef fc1 y ys => getFromClause !ys
    IParameters fc1 ys zs => rawImpFromDecl !zs ++ map getParamTy ys
    IRecord fc1 y z (MkImpRecord fc n params conName fields) => do
        (a, b) <- map (snd . snd) params
        getFromPiInfo a ++ [b] ++ getFromIField !fields
    INamespace fc1 ys zs => rawImpFromDecl !zs
    ITransform fc1 y z w => [z, w]
    IRunElabDecl fc1 y => [] -- Not sure about this either
    IPragma _ f => []
    ILog k => []
    IBuiltin _ _ _ => []
  where getParamTy : (a, b, c, RawImp) -> RawImp
        getParamTy (_, _, _, ty) = ty
        getFromTy : ImpTy -> RawImp
        getFromTy (MkImpTy _ _ _ ty) = ty
        getFromClause : ImpClause -> List RawImp
        getFromClause (PatClause fc1 lhs rhs) = [lhs, rhs]
        getFromClause (WithClause fc1 lhs wval prf flags ys) = [wval, lhs] ++ getFromClause !ys
        getFromClause (ImpossibleClause fc1 lhs) = [lhs]
        getFromPiInfo : PiInfo RawImp -> List RawImp
        getFromPiInfo (DefImplicit x) = [x]
        getFromPiInfo _ = []
        getFromIField : IField -> List RawImp
        getFromIField (MkIField fc x y z w) = getFromPiInfo y ++ [w]


-- Identify lower case names in argument position, which we can bind later.
-- Don't go under case, let, or local bindings, or IAlternative.
--
-- arg: Is the current expression in argument position? (We don't want to implicitly
--      bind funtions.)
--
-- env: Local names in scope. We only want to bind free variables, so we need this.
export
findBindableNames : (arg : Bool) -> (env : List Name) -> (used : List String) ->
                    RawImp -> List (String, String)

-- Helper to traverse the inside of a quoted expression, looking for unquotes
findBindableNamesQuot : List Name -> (used : List String) -> RawImp ->
                        List (String, String)

findBindableNames True env used (IVar fc nm@(UN (Basic n)))
      -- If the identifier is not bound locally and begins with a lowercase letter..
    = if not (nm `elem` env) && lowerFirst n
         then [(n, genUniqueStr used n)]
         else []
findBindableNames arg env used (IPi fc rig p mn aty retty)
    = let env' = case mn of
                      Nothing => env
                      Just n => n :: env in
          findBindableNames True env used aty ++
          findBindableNames True env' used retty
findBindableNames arg env used (ILam fc rig p mn aty sc)
    = let env' = case mn of
                      Nothing => env
                      Just n => n :: env in
      findBindableNames True env used aty ++
      findBindableNames True env' used sc
findBindableNames arg env used (IApp fc fn av)
    = findBindableNames False env used fn ++ findBindableNames True env used av
findBindableNames arg env used (INamedApp fc fn n av)
    = findBindableNames False env used fn ++ findBindableNames True env used av
findBindableNames arg env used (IAutoApp fc fn av)
    = findBindableNames False env used fn ++ findBindableNames True env used av
findBindableNames arg env used (IWithApp fc fn av)
    = findBindableNames False env used fn ++ findBindableNames True env used av
findBindableNames arg env used (IAs fc _ _ (UN (Basic n)) pat)
    = (n, genUniqueStr used n) :: findBindableNames arg env used pat
findBindableNames arg env used (IAs fc _ _ n pat)
    = findBindableNames arg env used pat
findBindableNames arg env used (IMustUnify fc r pat)
    = findBindableNames arg env used pat
findBindableNames arg env used (IDelayed fc r t)
    = findBindableNames arg env used t
findBindableNames arg env used (IDelay fc t)
    = findBindableNames arg env used t
findBindableNames arg env used (IForce fc t)
    = findBindableNames arg env used t
findBindableNames arg env used (IQuote fc t)
    = findBindableNamesQuot env used t
findBindableNames arg env used (IQuoteDecl fc d)
    = findBindableNamesQuot env used !(rawImpFromDecl !d)
findBindableNames arg env used (IAlternative fc u alts)
    = concatMap (findBindableNames arg env used) alts
findBindableNames arg env used (IUpdate fc updates tm)
    = findBindableNames True env used tm ++
      concatMap (findBindableNames True env used . getFieldUpdateTerm) updates
-- We've skipped case, let and local - rather than guess where the
-- name should be bound, leave it to the programmer
findBindableNames arg env used tm = []

findBindableNamesQuot env used (IPi fc x y z argTy retTy)
    = findBindableNamesQuot env used ![argTy, retTy]
findBindableNamesQuot env used (ILam fc x y z argTy lamTy)
    = findBindableNamesQuot env used ![argTy, lamTy]
findBindableNamesQuot env used (ILet fc lhsfc x y nTy nVal scope)
    = findBindableNamesQuot env used ![nTy, nVal, scope]
findBindableNamesQuot env used (ICase fc x ty xs)
    = findBindableNamesQuot env used !([x, ty] ++ getRawImp !xs)
  where getRawImp : ImpClause -> List RawImp
        getRawImp (PatClause fc1 lhs rhs) = [lhs, rhs]
        getRawImp (WithClause fc1 lhs wval prf flags ys) = [wval, lhs] ++ getRawImp !ys
        getRawImp (ImpossibleClause fc1 lhs) = [lhs]
findBindableNamesQuot env used (ILocal fc xs x)
    = findBindableNamesQuot env used !(x :: rawImpFromDecl !xs)
findBindableNamesQuot env used (ICaseLocal fc uname internalName args x)
    = findBindableNamesQuot env used x
findBindableNamesQuot env used (IApp fc x y)
    = findBindableNamesQuot env used ![x, y]
findBindableNamesQuot env used (INamedApp fc x y z)
    = findBindableNamesQuot env used ![x, z]
findBindableNamesQuot env used (IAutoApp fc x y)
    = findBindableNamesQuot env used ![x, y]
findBindableNamesQuot env used (IWithApp fc x y)
    = findBindableNamesQuot env used ![x, y]
findBindableNamesQuot env used (IRewrite fc x y)
    = findBindableNamesQuot env used ![x, y]
findBindableNamesQuot env used (ICoerced fc x)
    = findBindableNamesQuot env used x
findBindableNamesQuot env used (IBindHere fc x y)
    = findBindableNamesQuot env used y
findBindableNamesQuot env used (IUpdate fc xs x)
    = findBindableNamesQuot env used !(x :: map getFieldUpdateTerm xs)
findBindableNamesQuot env used (IAs fc nfc x y z)
    = findBindableNamesQuot env used z
findBindableNamesQuot env used (IDelayed fc x y)
    = findBindableNamesQuot env used y
findBindableNamesQuot env used (IDelay fc x)
    = findBindableNamesQuot env used x
findBindableNamesQuot env used (IForce fc x)
    = findBindableNamesQuot env used x
findBindableNamesQuot env used (IUnquote fc x)
    = findBindableNames True env used x
findBindableNamesQuot env used (IWithUnambigNames fc xs x)
    = findBindableNamesQuot env used x
findBindableNamesQuot env used (IVar fc x) = []
findBindableNamesQuot env used (ISearch fc depth) = []
findBindableNamesQuot env used (IAlternative fc x xs) = []
findBindableNamesQuot env used (IBindVar fc x) = []
findBindableNamesQuot env used (IPrimVal fc c) = []
findBindableNamesQuot env used (IType fc) = []
findBindableNamesQuot env used (IHole fc x) = []
findBindableNamesQuot env used (Implicit fc bindIfUnsolved) = []
-- These are the ones I'm not sure about
findBindableNamesQuot env used (IMustUnify fc x y)
    = findBindableNamesQuot env used y
findBindableNamesQuot env used (IUnifyLog fc k x)
    = findBindableNamesQuot env used x
-- Should f `(g `(List ~(x))) bind "x" as a parameter to "f"?
-- Depends how (or if) recursive quoting works
findBindableNamesQuot env used (IQuote fc x) = []
findBindableNamesQuot env used (IQuoteName fc x) = []
findBindableNamesQuot env used (IQuoteDecl fc xs) = []
findBindableNamesQuot env used (IRunElab fc x) = []

export
findUniqueBindableNames :
  {auto c : Ref Ctxt Defs} ->
  FC -> (arg : Bool) -> (env : List Name) -> (used : List String) ->
  RawImp -> Core (List (String, String))
findUniqueBindableNames fc arg env used t
  = do let assoc = nub (findBindableNames arg env used t)
       when (showShadowingWarning !getSession) $
         do defs <- get Ctxt
            let ctxt = gamma defs
            ns <- map catMaybes $ for assoc $ \ (n, _) => do
                    ns <- lookupCtxtName (UN (Basic n)) ctxt
                    let ns = flip mapMaybe ns $ \(n, _, d) =>
                               case definition d of
                                -- do not warn about holes: `?a` is not actually
                                -- getting shadowed as it will not become a
                                -- toplevel declaration
                                 Hole _ _ => Nothing
                                 _ => pure n
                    pure $ MkPair n <$> fromList ns
            whenJust (fromList ns) $ recordWarning . ShadowingGlobalDefs fc
       pure assoc

export
findAllNames : (env : List Name) -> RawImp -> List Name
findAllNames env (IVar fc n)
    = if not (n `elem` env) then [n] else []
findAllNames env (IPi fc rig p mn aty retty)
    = let env' = case mn of
                      Nothing => env
                      Just n => n :: env in
          findAllNames env aty ++ findAllNames env' retty
findAllNames env (ILam fc rig p mn aty sc)
    = let env' = case mn of
                      Nothing => env
                      Just n => n :: env in
      findAllNames env' aty ++ findAllNames env' sc
findAllNames env (IApp fc fn av)
    = findAllNames env fn ++ findAllNames env av
findAllNames env (INamedApp fc fn n av)
    = findAllNames env fn ++ findAllNames env av
findAllNames env (IAutoApp fc fn av)
    = findAllNames env fn ++ findAllNames env av
findAllNames env (IWithApp fc fn av)
    = findAllNames env fn ++ findAllNames env av
findAllNames env (IAs fc _ _ n pat)
    = n :: findAllNames env pat
findAllNames env (IMustUnify fc r pat)
    = findAllNames env pat
findAllNames env (IDelayed fc r t)
    = findAllNames env t
findAllNames env (IDelay fc t)
    = findAllNames env t
findAllNames env (IForce fc t)
    = findAllNames env t
findAllNames env (IQuote fc t)
    = findAllNames env t
findAllNames env (IUnquote fc t)
    = findAllNames env t
findAllNames env (IAlternative fc u alts)
    = concatMap (findAllNames env) alts
findAllNames env (IUpdate fc updates tm)
    = findAllNames env tm
    ++ concatMap (findAllNames env . getFieldUpdateTerm) updates
    ++ concatMap (map (UN . Basic) . getFieldUpdatePath) updates
-- We've skipped case, let and local - rather than guess where the
-- name should be bound, leave it to the programmer
findAllNames env tm = []

-- Find the names in a type that affect the 'using' declarations (i.e.
-- the ones that mean the declaration will be added).
export
findIBindVars : RawImp -> List Name
findIBindVars (IPi fc rig p mn aty retty)
    = findIBindVars aty ++ findIBindVars retty
findIBindVars (ILam fc rig p mn aty sc)
    = findIBindVars aty ++ findIBindVars sc
findIBindVars (IApp fc fn av)
    = findIBindVars fn ++ findIBindVars av
findIBindVars (INamedApp fc fn n av)
    = findIBindVars fn ++ findIBindVars av
findIBindVars (IAutoApp fc fn av)
    = findIBindVars fn ++ findIBindVars av
findIBindVars (IWithApp fc fn av)
    = findIBindVars fn ++ findIBindVars av
findIBindVars (IBindVar fc v)
    = [UN (Basic v)]
findIBindVars (IDelayed fc r t)
    = findIBindVars t
findIBindVars (IDelay fc t)
    = findIBindVars t
findIBindVars (IForce fc t)
    = findIBindVars t
findIBindVars (IAlternative fc u alts)
    = concatMap findIBindVars alts
findIBindVars (IUpdate fc updates tm)
    = findIBindVars tm ++ concatMap (findIBindVars . getFieldUpdateTerm) updates
-- We've skipped case, let and local - rather than guess where the
-- name should be bound, leave it to the programmer
findIBindVars tm = []

mutual
  -- Substitute for either an explicit variable name, or a bound variable name
  substNames' : Bool -> List Name -> List (Name, RawImp) ->
                RawImp -> RawImp
  substNames' False bound ps (IVar fc n)
      = if not (n `elem` bound)
           then case lookup n ps of
                     Just t => t
                     _ => IVar fc n
           else IVar fc n
  substNames' True bound ps (IBindVar fc n)
      = if not (UN (Basic n) `elem` bound)
           then case lookup (UN $ Basic n) ps of
                     Just t => t
                     _ => IBindVar fc n
           else IBindVar fc n
  substNames' bvar bound ps (IPi fc r p mn argTy retTy)
      = let bound' = maybe bound (\n => n :: bound) mn in
            IPi fc r p mn (substNames' bvar bound ps argTy)
                          (substNames' bvar bound' ps retTy)
  substNames' bvar bound ps (ILam fc r p mn argTy scope)
      = let bound' = maybe bound (\n => n :: bound) mn in
            ILam fc r p mn (substNames' bvar bound ps argTy)
                           (substNames' bvar bound' ps scope)
  substNames' bvar bound ps (ILet fc lhsFC r n nTy nVal scope)
      = let bound' = n :: bound in
            ILet fc lhsFC r n (substNames' bvar bound ps nTy)
                              (substNames' bvar bound ps nVal)
                              (substNames' bvar bound' ps scope)
  substNames' bvar bound ps (ICase fc y ty xs)
      = ICase fc (substNames' bvar bound ps y) (substNames' bvar bound ps ty)
                 (map (substNamesClause' bvar bound ps) xs)
  substNames' bvar bound ps (ILocal fc xs y)
      = let bound' = definedInBlock emptyNS xs ++ bound in
            ILocal fc (map (substNamesDecl' bvar bound ps) xs)
                      (substNames' bvar bound' ps y)
  substNames' bvar bound ps (IApp fc fn arg)
      = IApp fc (substNames' bvar bound ps fn) (substNames' bvar bound ps arg)
  substNames' bvar bound ps (INamedApp fc fn y arg)
      = INamedApp fc (substNames' bvar bound ps fn) y (substNames' bvar bound ps arg)
  substNames' bvar bound ps (IAutoApp fc fn arg)
      = IAutoApp fc (substNames' bvar bound ps fn) (substNames' bvar bound ps arg)
  substNames' bvar bound ps (IWithApp fc fn arg)
      = IWithApp fc (substNames' bvar bound ps fn) (substNames' bvar bound ps arg)
  substNames' bvar bound ps (IAlternative fc y xs)
      = IAlternative fc y (map (substNames' bvar bound ps) xs)
  substNames' bvar bound ps (ICoerced fc y)
      = ICoerced fc (substNames' bvar bound ps y)
  substNames' bvar bound ps (IAs fc nameFC s y pattern)
      = IAs fc nameFC s y (substNames' bvar bound ps pattern)
  substNames' bvar bound ps (IMustUnify fc r pattern)
      = IMustUnify fc r (substNames' bvar bound ps pattern)
  substNames' bvar bound ps (IDelayed fc r t)
      = IDelayed fc r (substNames' bvar bound ps t)
  substNames' bvar bound ps (IDelay fc t)
      = IDelay fc (substNames' bvar bound ps t)
  substNames' bvar bound ps (IForce fc t)
      = IForce fc (substNames' bvar bound ps t)
  substNames' bvar bound ps (IUpdate fc updates tm)
      = IUpdate fc (map (mapFieldUpdateTerm $ substNames' bvar bound ps) updates)
                   (substNames' bvar bound ps tm)
  substNames' bvar bound ps tm = tm

  substNamesClause' : Bool -> List Name -> List (Name, RawImp) ->
                      ImpClause -> ImpClause
  substNamesClause' bvar bound ps (PatClause fc lhs rhs)
      = let bound' = map (UN . Basic) (map snd (findBindableNames True bound [] lhs))
                     ++ findIBindVars lhs
                     ++ bound in
            PatClause fc (substNames' bvar [] [] lhs)
                         (substNames' bvar bound' ps rhs)
  substNamesClause' bvar bound ps (WithClause fc lhs wval prf flags cs)
      = let bound' = map (UN . Basic) (map snd (findBindableNames True bound [] lhs))
                     ++ findIBindVars lhs
                     ++ bound in
            WithClause fc (substNames' bvar [] [] lhs)
                          (substNames' bvar bound' ps wval) prf flags cs
  substNamesClause' bvar bound ps (ImpossibleClause fc lhs)
      = ImpossibleClause fc (substNames' bvar bound [] lhs)

  substNamesTy' : Bool -> List Name -> List (Name, RawImp) ->
                  ImpTy -> ImpTy
  substNamesTy' bvar bound ps (MkImpTy fc nameFC n ty)
      = MkImpTy fc nameFC n (substNames' bvar bound ps ty)

  substNamesData' : Bool -> List Name -> List (Name, RawImp) ->
                    ImpData -> ImpData
  substNamesData' bvar bound ps (MkImpData fc n con opts dcons)
      = MkImpData fc n (substNames' bvar bound ps con) opts
                  (map (substNamesTy' bvar bound ps) dcons)
  substNamesData' bvar bound ps (MkImpLater fc n con)
      = MkImpLater fc n (substNames' bvar bound ps con)

  substNamesDecl' : Bool -> List Name -> List (Name, RawImp ) ->
                   ImpDecl -> ImpDecl
  substNamesDecl' bvar bound ps (IClaim fc r vis opts td)
      = IClaim fc r vis opts (substNamesTy' bvar bound ps td)
  substNamesDecl' bvar bound ps (IDef fc n cs)
      = IDef fc n (map (substNamesClause' bvar bound ps) cs)
  substNamesDecl' bvar bound ps (IData fc vis d)
      = IData fc vis (substNamesData' bvar bound ps d)
  substNamesDecl' bvar bound ps (INamespace fc ns ds)
      = INamespace fc ns (map (substNamesDecl' bvar bound ps) ds)
  substNamesDecl' bvar bound ps d = d

export
substNames : List Name -> List (Name, RawImp) ->
             RawImp -> RawImp
substNames = substNames' False

export
substBindVars : List Name -> List (Name, RawImp) ->
                RawImp -> RawImp
substBindVars = substNames' True

export
substNamesClause : List Name -> List (Name, RawImp) ->
                   ImpClause -> ImpClause
substNamesClause = substNamesClause' False

mutual
  export
  substLoc : FC -> RawImp -> RawImp
  substLoc fc' (IVar fc n) = IVar fc' n
  substLoc fc' (IPi fc r p mn argTy retTy)
      = IPi fc' r p mn (substLoc fc' argTy)
                      (substLoc fc' retTy)
  substLoc fc' (ILam fc r p mn argTy scope)
      = ILam fc' r p mn (substLoc fc' argTy)
                        (substLoc fc' scope)
  substLoc fc' (ILet fc lhsFC r n nTy nVal scope)
      = ILet fc' fc' r n (substLoc fc' nTy)
                     (substLoc fc' nVal)
                     (substLoc fc' scope)
  substLoc fc' (ICase fc y ty xs)
      = ICase fc' (substLoc fc' y) (substLoc fc' ty)
                  (map (substLocClause fc') xs)
  substLoc fc' (ILocal fc xs y)
      = ILocal fc' (map (substLocDecl fc') xs)
                   (substLoc fc' y)
  substLoc fc' (IApp fc fn arg)
      = IApp fc' (substLoc fc' fn) (substLoc fc' arg)
  substLoc fc' (INamedApp fc fn y arg)
      = INamedApp fc' (substLoc fc' fn) y (substLoc fc' arg)
  substLoc fc' (IAutoApp fc fn arg)
      = IAutoApp fc' (substLoc fc' fn) (substLoc fc' arg)
  substLoc fc' (IWithApp fc fn arg)
      = IWithApp fc' (substLoc fc' fn) (substLoc fc' arg)
  substLoc fc' (IAlternative fc y xs)
      = IAlternative fc' y (map (substLoc fc') xs)
  substLoc fc' (ICoerced fc y)
      = ICoerced fc' (substLoc fc' y)
  substLoc fc' (IAs fc nameFC s y pattern)
      = IAs fc' fc' s y (substLoc fc' pattern)
  substLoc fc' (IMustUnify fc r pattern)
      = IMustUnify fc' r (substLoc fc' pattern)
  substLoc fc' (IDelayed fc r t)
      = IDelayed fc' r (substLoc fc' t)
  substLoc fc' (IDelay fc t)
      = IDelay fc' (substLoc fc' t)
  substLoc fc' (IForce fc t)
      = IForce fc' (substLoc fc' t)
  substLoc fc' (IUpdate fc updates tm)
      = IUpdate fc' (map (mapFieldUpdateTerm $ substLoc fc') updates)
                    (substLoc fc' tm)
  substLoc fc' tm = tm

  export
  substLocClause : FC -> ImpClause -> ImpClause
  substLocClause fc' (PatClause fc lhs rhs)
      = PatClause fc' (substLoc fc' lhs)
                      (substLoc fc' rhs)
  substLocClause fc' (WithClause fc lhs wval prf flags cs)
      = WithClause fc' (substLoc fc' lhs)
                       (substLoc fc' wval)
                       prf
                       flags
                       (map (substLocClause fc') cs)
  substLocClause fc' (ImpossibleClause fc lhs)
      = ImpossibleClause fc' (substLoc fc' lhs)

  substLocTy : FC -> ImpTy -> ImpTy
  substLocTy fc' (MkImpTy fc nameFC n ty)
      = MkImpTy fc' fc' n (substLoc fc' ty)

  substLocData : FC -> ImpData -> ImpData
  substLocData fc' (MkImpData fc n con opts dcons)
      = MkImpData fc' n (substLoc fc' con) opts
                        (map (substLocTy fc') dcons)
  substLocData fc' (MkImpLater fc n con)
      = MkImpLater fc' n (substLoc fc' con)

  substLocDecl : FC -> ImpDecl -> ImpDecl
  substLocDecl fc' (IClaim fc r vis opts td)
      = IClaim fc' r vis opts (substLocTy fc' td)
  substLocDecl fc' (IDef fc n cs)
      = IDef fc' n (map (substLocClause fc') cs)
  substLocDecl fc' (IData fc vis d)
      = IData fc' vis (substLocData fc' d)
  substLocDecl fc' (INamespace fc ns ds)
      = INamespace fc' ns (map (substLocDecl fc') ds)
  substLocDecl fc' d = d

nameNum : String -> (String, Maybe Int)
nameNum str = case span isDigit (reverse str) of
  ("", _) => (str, Nothing)
  (nums, pre) => case unpack pre of
    ('_' :: rest) => (reverse (pack rest), Just $ cast (reverse nums))
    _ => (str, Nothing)

nextNameNum : (String, Maybe Int) -> (String, Maybe Int)
nextNameNum (str, mn) = (str, Just $ maybe 0 (1+) mn)

unNameNum : (String, Maybe Int) -> String
unNameNum (str, Nothing) = str
unNameNum (str, Just n) = fastConcat [str, "_", show n]


export
uniqueBasicName : Defs -> List String -> String -> Core String
uniqueBasicName defs used n
    = if !usedName
         then uniqueBasicName defs used (next n)
         else pure n
  where
    usedName : Core Bool
    usedName
        = pure $ case !(lookupTyName (UN $ Basic n) (gamma defs)) of
                      [] => n `elem` used
                      _ => True

    next : String -> String
    next = unNameNum . nextNameNum . nameNum

export
uniqueHoleName : {auto s : Ref Syn SyntaxInfo} ->
                 Defs -> List String -> String -> Core String
uniqueHoleName defs used n
    = do syn <- get Syn
         uniqueBasicName defs (used ++ holeNames syn) n
