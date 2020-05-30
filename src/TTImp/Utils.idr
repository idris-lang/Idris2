module TTImp.Utils

import Core.Context
import Core.TT
import TTImp.TTImp

import Data.List
import Data.Strings

%default covering

lowerFirst : String -> Bool
lowerFirst "" = False
lowerFirst str = assert_total (isLower (prim__strHead str))

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
          findBindableNames True env' used aty ++
          findBindableNames True env' used retty
findBindableNames arg env used (ILam fc rig p mn aty sc)
    = let env' = case mn of
                      Nothing => env
                      Just n => n :: env in
      findBindableNames True env' used aty ++
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
findBindableNames arg env used (IAlternative fc u alts)
    = concatMap (findBindableNames arg env used) alts
-- We've skipped case, let and local - rather than guess where the
-- name should be bound, leave it to the programmer
findBindableNames arg env used tm = []

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
  export
  substNames : List Name -> List (Name, RawImp) ->
               RawImp -> RawImp
  substNames bound ps (IVar fc n)
      = if not (n `elem` bound)
           then case lookup n ps of
                     Just t => t
                     _ => IVar fc n
           else IVar fc n
  substNames bound ps (IPi fc r p mn argTy retTy)
      = let bound' = maybe bound (\n => n :: bound) mn in
            IPi fc r p mn (substNames bound ps argTy)
                          (substNames bound' ps retTy)
  substNames bound ps (ILam fc r p mn argTy scope)
      = let bound' = maybe bound (\n => n :: bound) mn in
            ILam fc r p mn (substNames bound ps argTy)
                           (substNames bound' ps scope)
  substNames bound ps (ILet fc r n nTy nVal scope)
      = let bound' = n :: bound in
            ILet fc r n (substNames bound ps nTy)
                        (substNames bound ps nVal)
                        (substNames bound' ps scope)
  substNames bound ps (ICase fc y ty xs)
      = ICase fc (substNames bound ps y) (substNames bound ps ty)
                 (map (substNamesClause bound ps) xs)
  substNames bound ps (ILocal fc xs y)
      = let bound' = definedInBlock [] xs ++ bound in
            ILocal fc (map (substNamesDecl bound ps) xs)
                      (substNames bound' ps y)
  substNames bound ps (IApp fc fn arg)
      = IApp fc (substNames bound ps fn) (substNames bound ps arg)
  substNames bound ps (IImplicitApp fc fn y arg)
      = IImplicitApp fc (substNames bound ps fn) y (substNames bound ps arg)
  substNames bound ps (IWithApp fc fn arg)
      = IWithApp fc (substNames bound ps fn) (substNames bound ps arg)
  substNames bound ps (IAlternative fc y xs)
      = IAlternative fc y (map (substNames bound ps) xs)
  substNames bound ps (ICoerced fc y)
      = ICoerced fc (substNames bound ps y)
  substNames bound ps (IAs fc s y pattern)
      = IAs fc s y (substNames bound ps pattern)
  substNames bound ps (IMustUnify fc r pattern)
      = IMustUnify fc r (substNames bound ps pattern)
  substNames bound ps (IDelayed fc r t)
      = IDelayed fc r (substNames bound ps t)
  substNames bound ps (IDelay fc t)
      = IDelay fc (substNames bound ps t)
  substNames bound ps (IForce fc t)
      = IForce fc (substNames bound ps t)
  substNames bound ps tm = tm

  export
  substNamesClause : List Name -> List (Name, RawImp) ->
                     ImpClause -> ImpClause
  substNamesClause bound ps (PatClause fc lhs rhs)
      = let bound' = map UN (map snd (findBindableNames True bound [] lhs))
                        ++ bound in
            PatClause fc (substNames [] [] lhs)
                         (substNames bound' ps rhs)
  substNamesClause bound ps (WithClause fc lhs wval flags cs)
      = let bound' = map UN (map snd (findBindableNames True bound [] lhs))
                        ++ bound in
            WithClause fc (substNames [] [] lhs)
                          (substNames bound' ps wval) flags cs
  substNamesClause bound ps (ImpossibleClause fc lhs)
      = ImpossibleClause fc (substNames bound [] lhs)

  substNamesTy : List Name -> List (Name, RawImp) ->
                  ImpTy -> ImpTy
  substNamesTy bound ps (MkImpTy fc n ty)
      = MkImpTy fc n (substNames bound ps ty)

  substNamesData : List Name -> List (Name, RawImp) ->
                   ImpData -> ImpData
  substNamesData bound ps (MkImpData fc n con opts dcons)
      = MkImpData fc n (substNames bound ps con) opts
                  (map (substNamesTy bound ps) dcons)
  substNamesData bound ps (MkImpLater fc n con)
      = MkImpLater fc n (substNames bound ps con)

  substNamesDecl : List Name -> List (Name, RawImp ) ->
                   ImpDecl -> ImpDecl
  substNamesDecl bound ps (IClaim fc r vis opts td)
      = IClaim fc r vis opts (substNamesTy bound ps td)
  substNamesDecl bound ps (IDef fc n cs)
      = IDef fc n (map (substNamesClause bound ps) cs)
  substNamesDecl bound ps (IData fc vis d)
      = IData fc vis (substNamesData bound ps d)
  substNamesDecl bound ps (INamespace fc ns ds)
      = INamespace fc ns (map (substNamesDecl bound ps) ds)
  substNamesDecl bound ps d = d

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
        = case !(lookupTyName (UN n) (gamma defs)) of
               [] => pure $ n `elem` used
               _ => pure True

    next : String -> String
    next str
        = let (n, i) = nameNum str in
              n ++ "_" ++ show (i + 1)

export
checkRefVisibility : {auto c : Ref Ctxt Defs} ->
                     FC -> Name ->
                     Visibility -> -- Visibility of the name
                     Visibility -> -- Minimum visibility of references
                     Name -> Core ()
checkRefVisibility fc fn vis min ref
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact ref (gamma defs)
              | Nothing => pure ()
         when (visibility gdef <= min) $
              throw (VisibilityError fc vis fn (visibility gdef) ref)
