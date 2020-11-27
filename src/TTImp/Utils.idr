module TTImp.Utils

import Core.Context
import Core.TT
import TTImp.TTImp

import Data.List
import Data.Strings

import Utils.String

%default covering

export
getUnique : List String -> String -> String
getUnique xs x = if x `elem` xs then getUnique xs (x ++ "'") else x

-- Bind lower case names in argument position
-- Don't go under case, let, or local bindings, or IAlternative
export
findBindableNames : (arg : Bool) -> List Name -> (used : List String) ->
                    RawImp -> List (String, String)
findBindableNames True env used (IVar fc (UN n))
    = if not (UN n `elem` env) && lowerFirst n
         then [(n, getUnique used n)]
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
findBindableNames arg env used (IImplicitApp fc fn n av)
    = findBindableNames False env used fn ++ findBindableNames True env used av
findBindableNames arg env used (IWithApp fc fn av)
    = findBindableNames False env used fn ++ findBindableNames True env used av
findBindableNames arg env used (IAs fc _ (UN n) pat)
    = (n, getUnique used n) :: findBindableNames arg env used pat
findBindableNames arg env used (IAs fc _ n pat)
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
    = findBindableNames arg env used t
findBindableNames arg env used (IUnquote fc t)
    = findBindableNames arg env used t
findBindableNames arg env used (IAlternative fc u alts)
    = concatMap (findBindableNames arg env used) alts
-- We've skipped case, let and local - rather than guess where the
-- name should be bound, leave it to the programmer
findBindableNames arg env used tm = []

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
findAllNames env (IImplicitApp fc fn n av)
    = findAllNames env fn ++ findAllNames env av
findAllNames env (IWithApp fc fn av)
    = findAllNames env fn ++ findAllNames env av
findAllNames env (IAs fc _ n pat)
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
findIBindVars (IImplicitApp fc fn n av)
    = findIBindVars fn ++ findIBindVars av
findIBindVars (IWithApp fc fn av)
    = findIBindVars fn ++ findIBindVars av
findIBindVars (IBindVar fc v)
    = [UN v]
findIBindVars (IDelayed fc r t)
    = findIBindVars t
findIBindVars (IDelay fc t)
    = findIBindVars t
findIBindVars (IForce fc t)
    = findIBindVars t
findIBindVars (IAlternative fc u alts)
    = concatMap findIBindVars alts
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
      = if not (UN n `elem` bound)
           then case lookup (UN n) ps of
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
  substNames' bvar bound ps (ILet fc r n nTy nVal scope)
      = let bound' = n :: bound in
            ILet fc r n (substNames' bvar bound ps nTy)
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
  substNames' bvar bound ps (IImplicitApp fc fn y arg)
      = IImplicitApp fc (substNames' bvar bound ps fn) y (substNames' bvar bound ps arg)
  substNames' bvar bound ps (IWithApp fc fn arg)
      = IWithApp fc (substNames' bvar bound ps fn) (substNames' bvar bound ps arg)
  substNames' bvar bound ps (IAlternative fc y xs)
      = IAlternative fc y (map (substNames' bvar bound ps) xs)
  substNames' bvar bound ps (ICoerced fc y)
      = ICoerced fc (substNames' bvar bound ps y)
  substNames' bvar bound ps (IAs fc s y pattern)
      = IAs fc s y (substNames' bvar bound ps pattern)
  substNames' bvar bound ps (IMustUnify fc r pattern)
      = IMustUnify fc r (substNames' bvar bound ps pattern)
  substNames' bvar bound ps (IDelayed fc r t)
      = IDelayed fc r (substNames' bvar bound ps t)
  substNames' bvar bound ps (IDelay fc t)
      = IDelay fc (substNames' bvar bound ps t)
  substNames' bvar bound ps (IForce fc t)
      = IForce fc (substNames' bvar bound ps t)
  substNames' bvar bound ps tm = tm

  substNamesClause' : Bool -> List Name -> List (Name, RawImp) ->
                      ImpClause -> ImpClause
  substNamesClause' bvar bound ps (PatClause fc lhs rhs)
      = let bound' = map UN (map snd (findBindableNames True bound [] lhs))
                        ++ bound in
            PatClause fc (substNames' bvar [] [] lhs)
                         (substNames' bvar bound' ps rhs)
  substNamesClause' bvar bound ps (WithClause fc lhs wval flags cs)
      = let bound' = map UN (map snd (findBindableNames True bound [] lhs))
                        ++ bound in
            WithClause fc (substNames' bvar [] [] lhs)
                          (substNames' bvar bound' ps wval) flags cs
  substNamesClause' bvar bound ps (ImpossibleClause fc lhs)
      = ImpossibleClause fc (substNames' bvar bound [] lhs)

  substNamesTy' : Bool -> List Name -> List (Name, RawImp) ->
                  ImpTy -> ImpTy
  substNamesTy' bvar bound ps (MkImpTy fc n ty)
      = MkImpTy fc n (substNames' bvar bound ps ty)

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
  substLoc fc' (ILet fc r n nTy nVal scope)
      = ILet fc' r n (substLoc fc' nTy)
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
  substLoc fc' (IImplicitApp fc fn y arg)
      = IImplicitApp fc' (substLoc fc' fn) y (substLoc fc' arg)
  substLoc fc' (IWithApp fc fn arg)
      = IWithApp fc' (substLoc fc' fn) (substLoc fc' arg)
  substLoc fc' (IAlternative fc y xs)
      = IAlternative fc' y (map (substLoc fc') xs)
  substLoc fc' (ICoerced fc y)
      = ICoerced fc' (substLoc fc' y)
  substLoc fc' (IAs fc s y pattern)
      = IAs fc' s y (substLoc fc' pattern)
  substLoc fc' (IMustUnify fc r pattern)
      = IMustUnify fc' r (substLoc fc' pattern)
  substLoc fc' (IDelayed fc r t)
      = IDelayed fc' r (substLoc fc' t)
  substLoc fc' (IDelay fc t)
      = IDelay fc' (substLoc fc' t)
  substLoc fc' (IForce fc t)
      = IForce fc' (substLoc fc' t)
  substLoc fc' tm = tm

  export
  substLocClause : FC -> ImpClause -> ImpClause
  substLocClause fc' (PatClause fc lhs rhs)
      = PatClause fc' (substLoc fc' lhs)
                      (substLoc fc' rhs)
  substLocClause fc' (WithClause fc lhs wval flags cs)
      = WithClause fc' (substLoc fc' lhs)
                       (substLoc fc' wval)
                       flags
                       (map (substLocClause fc') cs)
  substLocClause fc' (ImpossibleClause fc lhs)
      = ImpossibleClause fc' (substLoc fc' lhs)

  substLocTy : FC -> ImpTy -> ImpTy
  substLocTy fc' (MkImpTy fc n ty)
      = MkImpTy fc' n (substLoc fc' ty)

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

nameNum : String -> (String, Int)
nameNum str
    = case span isDigit (reverse str) of
           ("", _) => (str, 0)
           (nums, pre)
              => case unpack pre of
                      ('_' :: rest) => (reverse (pack rest), cast (reverse nums))
                      _ => (str, 0)

export
uniqueName : Defs -> List String -> String -> Core String
uniqueName defs used n
    = if !usedName
         then uniqueName defs used (next n)
         else pure n
  where
    usedName : Core Bool
    usedName
        = pure $ case !(lookupTyName (UN n) (gamma defs)) of
                      [] => n `elem` used
                      _ => True

    next : String -> String
    next str
        = let (n, i) = nameNum str in
              n ++ "_" ++ show (i + 1)
