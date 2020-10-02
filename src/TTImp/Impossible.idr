module TTImp.Impossible

import Core.Context
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value

import TTImp.TTImp

import Data.List

%default covering

-- This file contains support for building a guess at the term on the LHS of an
-- 'impossible' case, in order to help build a tree of covered cases for
-- coverage checking. Since the LHS by definition won't be well typed, we are
-- only guessing! But we can still do some type-directed disambiguation of
-- names.
-- Constants (fromInteger/fromString etc) won't be supported, because in general
-- they involve resoling interfaces - they'll just become unmatchable patterns.

match : {auto c : Ref Ctxt Defs} ->
        NF [] -> (Name, Int, ClosedTerm) -> Core Bool
match nty (n, i, rty)
    = do defs <- get Ctxt
         rtynf <- nf defs [] rty
         sameRet nty rtynf
  where
    sameRet : NF [] -> NF [] -> Core Bool
    sameRet _ (NApp _ _ _) = pure True
    sameRet _ (NErased _ _) = pure True
    sameRet (NApp _ _ _) _ = pure True
    sameRet (NErased _ _) _ = pure True
    sameRet (NTCon _ n _ _ _) (NTCon _ n' _ _ _) = pure (n == n')
    sameRet (NPrimVal _ c) (NPrimVal _ c') = pure (c == c')
    sameRet (NType _) (NType _) = pure True
    sameRet nf (NBind fc _ (Pi _ _ _ _) sc)
        = do defs <- get Ctxt
             sc' <- sc defs (toClosure defaultOpts [] (Erased fc False))
             sameRet nf sc'
    sameRet _ _ = pure False

dropNoMatch : {auto c : Ref Ctxt Defs} ->
              Maybe (NF []) -> List (Name, Int, ClosedTerm) ->
              Core (List (Name, Int, ClosedTerm))
dropNoMatch _ [t] = pure [t]
dropNoMatch Nothing ts = pure ts
dropNoMatch (Just nty) ts
    = -- if the return type of a thing in ts doesn't match nty, drop it
      filterM (match nty) ts

nextVar : {auto q : Ref QVar Int} ->
          FC -> Core (Term [])
nextVar fc
    = do i <- get QVar
         put QVar (i + 1)
         pure (Ref fc Bound (MN "imp" i))

mutual
  processArgs : {auto c : Ref Ctxt Defs} ->
                {auto q : Ref QVar Int} ->
                Term [] -> NF [] ->
                (expargs : List RawImp) -> (impargs : List (Maybe Name, RawImp)) ->
                Core ClosedTerm
  processArgs fn (NBind fc x (Pi _ _ Explicit ty) sc) (e :: exp) imp
     = do e' <- mkTerm e (Just ty) [] []
          defs <- get Ctxt
          processArgs (App fc fn e') !(sc defs (toClosure defaultOpts [] e'))
                      exp imp
  processArgs fn (NBind fc x (Pi _ _ Implicit ty) sc) exp imp
     = do defs <- get Ctxt
          case useImp [] imp of
            Nothing => do e' <- nextVar fc
                          processArgs (App fc fn e')
                                      !(sc defs (toClosure defaultOpts [] e'))
                                      exp imp
            Just (e, impargs') =>
               do e' <- mkTerm e (Just ty) [] []
                  processArgs (App fc fn e') !(sc defs (toClosure defaultOpts [] e'))
                              exp impargs'
    where
      useImp : List (Maybe Name, RawImp) -> List (Maybe Name, RawImp) ->
               Maybe (RawImp, List (Maybe Name, RawImp))
      useImp acc [] = Nothing
      useImp acc ((Just x', xtm) :: rest)
          = if x == x'
               then Just (xtm, reverse acc ++ rest)
               else useImp ((Just x', xtm) :: acc) rest
      useImp acc (ximp :: rest)
          = useImp (ximp :: acc) rest
  processArgs fn (NBind fc x (Pi _ _ AutoImplicit ty) sc) exp imp
     = do defs <- get Ctxt
          case useAutoImp [] imp of
            Nothing => do e' <- nextVar fc
                          processArgs (App fc fn e')
                                      !(sc defs (toClosure defaultOpts [] e'))
                                      exp imp
            Just (e, impargs') =>
               do e' <- mkTerm e (Just ty) [] []
                  processArgs (App fc fn e') !(sc defs (toClosure defaultOpts [] e'))
                              exp impargs'
    where
      useAutoImp : List (Maybe Name, RawImp) -> List (Maybe Name, RawImp) ->
                   Maybe (RawImp, List (Maybe Name, RawImp))
      useAutoImp acc [] = Nothing
      useAutoImp acc ((Nothing, xtm) :: rest)
          = Just (xtm, reverse acc ++ rest)
      useAutoImp acc ((Just x', xtm) :: rest)
          = if x == x'
               then Just (xtm, reverse acc ++ rest)
               else useAutoImp ((Just x', xtm) :: acc) rest
      useAutoImp acc (ximp :: rest)
          = useAutoImp (ximp :: acc) rest
  processArgs fn ty [] [] = pure fn
  processArgs fn ty exp imp
     = throw (GenericMsg (getLoc fn)
                ("Badly formed impossible clause "
                     ++ show (fn, exp, imp)))

  buildApp : {auto c : Ref Ctxt Defs} ->
             {auto q : Ref QVar Int} ->
             FC -> Name -> Maybe (NF []) ->
             (expargs : List RawImp) -> (impargs : List (Maybe Name, RawImp)) ->
             Core ClosedTerm
  buildApp fc n mty exp imp
      = do defs <- get Ctxt
           prims <- getPrimitiveNames
           when (n `elem` prims) $
               throw (InternalError "Can't deal with constants here yet")

           tys <- lookupTyName n (gamma defs)
           [(n', _, ty)] <- dropNoMatch mty tys
              | [] => throw (UndefinedName fc n)
              | ts => throw (AmbiguousName fc (map fst ts))
           tynf <- nf defs [] ty
           processArgs (Ref fc Func n') tynf exp imp

  mkTerm : {auto c : Ref Ctxt Defs} ->
           {auto q : Ref QVar Int} ->
           RawImp -> Maybe (NF []) ->
           (expargs : List RawImp) -> (impargs : List (Maybe Name, RawImp)) ->
           Core ClosedTerm
  mkTerm (IVar fc n) mty exp imp
     = buildApp fc n mty exp imp
  mkTerm (IApp fc fn arg) mty exp imp
     = mkTerm fn mty (arg :: exp) imp
  mkTerm (IImplicitApp fc fn nm arg) mty exp imp
     = mkTerm fn mty exp ((nm, arg) :: imp)
  mkTerm (IPrimVal fc c) _ _ _ = pure (PrimVal fc c)
  mkTerm tm _ _ _ = nextVar (getFC tm)

-- Given an LHS that is declared 'impossible', build a term to match from,
-- so that when we build the case tree for checking coverage, we take into
-- account the impossible clauses
export
getImpossibleTerm : {vars : _} ->
                    {auto c : Ref Ctxt Defs} ->
                    Env Term vars -> NestedNames vars -> RawImp -> Core ClosedTerm
getImpossibleTerm env nest tm
    = do q <- newRef QVar (the Int 0)
         mkTerm (applyEnv tm) Nothing [] []
  where
    addEnv : {vars : _} ->
             FC -> Env Term vars -> List RawImp
    addEnv fc [] = []
    addEnv fc (b :: env) =
       if isLet b
          then addEnv fc env
          else Implicit fc False :: addEnv fc env

    expandNest : RawImp -> RawImp
    expandNest (IVar fc n)
        = case lookup n (names nest) of
               Just (Just n', _, _) => IVar fc n'
               _ => IVar fc n
    expandNest tm = tm

    -- Need to apply the function to the surrounding environment, and update
    -- the name to the proper one from the nested names map
    applyEnv : RawImp -> RawImp
    applyEnv (IApp fc fn arg) = IApp fc (applyEnv fn) arg
    applyEnv (IImplicitApp fc fn n arg)
        = IImplicitApp fc (applyEnv fn) n arg
    applyEnv tm = apply (expandNest tm) (addEnv (getFC tm) env)
