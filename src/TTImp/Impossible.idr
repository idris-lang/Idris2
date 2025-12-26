module TTImp.Impossible

import Core.Env
import Core.Value

import TTImp.TTImp
import TTImp.TTImp.Functor
import TTImp.Elab.App

import Idris.Syntax
import Idris.Resugar

%default covering

-- This file contains support for building a guess at the term on the LHS of an
-- 'impossible' case, in order to help build a tree of covered cases for
-- coverage checking. Since the LHS by definition won't be well typed, we are
-- only guessing! But we can still do some type-directed disambiguation of
-- names.
-- Constants (fromInteger/fromString etc) won't be supported, because in general
-- they involve resolving interfaces - they'll just become unmatchable patterns.

match : {auto c : Ref Ctxt Defs} ->
        ClosedNF -> (Name, Int, ClosedTerm) -> Core Bool
match nty (n, i, rty)
    = do defs <- get Ctxt
         rtynf <- nf defs Env.empty rty
         sameRet nty rtynf
  where
    sameRet : ClosedNF -> ClosedNF -> Core Bool
    sameRet _ (NApp {}) = pure True
    sameRet _ (NErased {}) = pure True
    sameRet (NApp {}) _ = pure True
    sameRet (NErased {}) _ = pure True
    sameRet (NTCon _ n _ _) (NTCon _ n' _ _) = pure (n == n')
    sameRet (NPrimVal _ c) (NPrimVal _ c') = pure (c == c')
    sameRet (NType {}) (NType {}) = pure True
    sameRet nf (NBind fc _ (Pi {}) sc)
        = do defs <- get Ctxt
             sc' <- sc defs (toClosure defaultOpts Env.empty (Erased fc Placeholder))
             sameRet nf sc'
    sameRet _ _ = pure False

dropNoMatch : {auto c : Ref Ctxt Defs} ->
              Maybe ClosedNF -> List (Name, Int, GlobalDef) ->
              Core (List (Name, Int, GlobalDef))
dropNoMatch Nothing ts = pure ts
dropNoMatch (Just nty) ts
    = -- if the return type of a thing in ts doesn't match nty, drop it
      filterM (match nty . map (map type)) ts

nextVar : {auto q : Ref QVar Int} ->
          FC -> Core ClosedTerm
nextVar fc
    = do i <- get QVar
         put QVar (i + 1)
         pure (Ref fc Bound (MN "imp" i))

badClause : {auto c : Ref Ctxt Defs} -> ClosedTerm -> List RawImp -> List RawImp -> List (Name, RawImp) -> Core a
badClause fn exps autos named
   = throw (GenericMsg (getLoc fn)
            ("Badly formed impossible clause "
               ++ show (!(toFullNames fn), exps, autos, named)))

mutual
  processArgs : {auto c : Ref Ctxt Defs} ->
                {auto s : Ref Syn SyntaxInfo} ->
                {auto q : Ref QVar Int} ->
                Bool -> -- should be fully applied
                ClosedTerm -> ClosedNF ->
                (expargs : List RawImp) ->
                (autoargs : List RawImp) ->
                (namedargs : List (Name, RawImp)) ->
                Core ClosedTerm
  -- unnamed takes priority
  processArgs con fn (NBind fc x (Pi _ _ Explicit ty) sc) (e :: exps) autos named
     = do e' <- mkTerm e (Just ty)
          defs <- get Ctxt
          processArgs con (App fc fn e')
                      !(sc defs (toClosure defaultOpts Env.empty e'))
                      exps autos named
  processArgs con fn (NBind fc x (Pi _ _ Explicit ty) sc) [] autos named
     = do defs <- get Ctxt
          case findNamed x named of
            Just ((_, e), named') =>
               do e' <- mkTerm e (Just ty)
                  processArgs con (App fc fn e')
                              !(sc defs (toClosure defaultOpts Env.empty e'))
                              [] autos named'
            Nothing => -- Expected an explicit argument, but only implicits left
                       do let False = con
                            | True => throw $ GenericMsg (getLoc fn) $
                                                "Cannot match on a partially applied constructor: "
                                                ++ show !(toFullNames fn)
                          let True = null autos && null named
                            | False => badClause fn [] autos named -- unexpected arguments
                          pure fn
  processArgs con fn (NBind fc x (Pi _ _ Implicit ty) sc) exps autos named
     = do defs <- get Ctxt
          case findNamed x named of
            Nothing => do e' <- nextVar fc
                          processArgs con (App fc fn e')
                                      !(sc defs (toClosure defaultOpts Env.empty e'))
                                      exps autos named
            Just ((_, e), named') =>
               do e' <- mkTerm e (Just ty)
                  processArgs con (App fc fn e')
                              !(sc defs (toClosure defaultOpts Env.empty e'))
                              exps autos named'
  processArgs con fn (NBind fc x (Pi _ _ AutoImplicit ty) sc) exps autos named
     = do defs <- get Ctxt
          case autos of
               (e :: autos') => -- unnamed takes priority
                   do e' <- mkTerm e (Just ty)
                      processArgs con (App fc fn e')
                                  !(sc defs (toClosure defaultOpts Env.empty e'))
                                  exps autos' named
               [] =>
                  case findNamed x named of
                     Nothing =>
                        do e' <- nextVar fc
                           processArgs con (App fc fn e')
                                       !(sc defs (toClosure defaultOpts Env.empty e'))
                                       exps [] named
                     Just ((_, e), named') =>
                        do e' <- mkTerm e (Just ty)
                           processArgs con (App fc fn e')
                                       !(sc defs (toClosure defaultOpts Env.empty e'))
                                       exps [] named'
  processArgs _ fn _ [] [] [] = pure fn
  processArgs _ fn _ (x :: _) autos named
     = throw $ GenericMsg (getFC x) "Too many arguments"
  processArgs _ fn _ exps autos named
     = badClause fn exps autos named

  buildApp : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto q : Ref QVar Int} ->
             FC -> Name -> Maybe ClosedClosure ->
             (expargs : List RawImp) ->
             (autoargs : List RawImp) ->
             (namedargs : List (Name, RawImp)) ->
             Core ClosedTerm
  buildApp fc n mty exps autos named
      = do defs <- get Ctxt
           prims <- getPrimitiveNames
           when (n `elem` prims) $
               throw (GenericMsg fc "Can't deal with \{show n} in impossible clauses yet")

           gdefs <- lookupNameBy id n (gamma defs)
           mty' <- traverseOpt (evalClosure defs) mty
           [(n', i, gdef)] <- dropNoMatch mty' gdefs
              | [] => if length gdefs == 0
                        then undefinedName fc n
                        else throw $ GenericMsg fc "\{show n} does not match expected type"
              | ts => throw $ AmbiguousName fc (map fst ts)
           tynf <- nf defs Env.empty (type gdef)
           -- #899 we need to make sure that type & data constructors are marked
           -- as such so that the coverage checker actually uses the matches in
           -- `impossible` branches to generate parts of the case tree.
           -- When `head` is `Func`, the pattern will be marked as forced and
           -- the coverage checker will considers that all the cases have been
           -- covered!
           let nameType = getDefNameType gdef
           processArgs (isJust $ isCon nameType)
                       (Ref fc nameType (Resolved i))
                       tynf exps autos named

  mkTerm : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto q : Ref QVar Int} ->
           RawImp -> Maybe ClosedClosure ->
           Core ClosedTerm
  mkTerm tm mty = go tm [] [] []
    where
      go : RawImp ->
          (expargs : List RawImp) ->
          (autoargs : List RawImp) ->
          (namedargs : List (Name, RawImp)) ->
          Core ClosedTerm
      go (IVar fc n) exps autos named
        = buildApp fc n mty exps autos named
      go (IAs fc fc' u n pat) exps autos named
        = go pat exps autos named
      go (IApp fc fn arg) exps autos named
        = go fn (arg :: exps) autos named
      go (IWithApp fc fn arg) exps autos named
        = go fn (arg :: exps) autos named
      go (IAutoApp fc fn arg) exps autos named
        = go fn exps (arg :: autos) named
      go (INamedApp fc fn nm arg) exps autos named
        = go fn exps autos ((nm, arg) :: named)
      go (IMustUnify fc r tm) exps autos named
        = Erased fc . Dotted <$> go tm exps autos named
      go (IPrimVal fc c) _ _ _
          = do let tm = PrimVal fc c
               True <- isValidPrimType
                 | _ => throw $ GenericMsg fc "\{show tm} does not match expected type"
               pure tm
        where
          isValidPrimType : Core Bool
          isValidPrimType
            = do defs <- get Ctxt
                 Just ty <- traverseOpt (evalClosure defs) mty
                   | _ => pure False
                 case (primType c, ty) of
                      (Nothing, NType {}) => pure True
                      (Just t1, NPrimVal _ (PrT t2)) => pure (t1 == t2)
                      _ => pure False
      go (IType fc) _ _ _
          = do defs <- get Ctxt
               Just (NType {}) <- traverseOpt (evalClosure defs) mty
                 | _ => throw $ GenericMsg fc "Type does not match expected type"
               pure (TType fc $ MN "top" 0)
      -- We're taking UniqueDefault here, _and_ we're falling through to error otherwise, which is sketchy.
      -- One option is to try each and emit an AmbiguousElab? We maybe should respect `UniqueDefault` if there
      -- is no evidence (mty), but we should _try_ to resolve here if there is an mty.
      go (IAlternative _ (UniqueDefault tm) _) exps autos named
        = go tm exps autos named
      go (Implicit fc _) _ _ _ = nextVar fc
      go (IBindVar fc _) _ _ _ = nextVar fc
      go tm _ _ _
        = do tm' <- pterm (map defaultKindedName tm) -- hack
             throw $ GenericMsg (getFC tm) "Unsupported term in impossible clause: \{show tm'}"

-- Given an LHS that is declared 'impossible', build a term to match from,
-- so that when we build the case tree for checking coverage, we take into
-- account the impossible clauses
export
getImpossibleTerm : {vars : _} ->
                    {auto c : Ref Ctxt Defs} ->
                    {auto s : Ref Syn SyntaxInfo} ->
                    Env Term vars -> NestedNames vars -> RawImp -> Core ClosedTerm
getImpossibleTerm env nest tm
    = do q <- newRef QVar (the Int 0)
         mkTerm (applyEnv tm) Nothing
  where
    addEnv : {vars : _} ->
             FC -> Env Term vars -> List RawImp
    addEnv fc [<] = []
    addEnv {vars = _ :< _} fc (env :< b) =
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
    applyEnv (IWithApp fc fn arg) = IWithApp fc (applyEnv fn) arg
    applyEnv (IAutoApp fc fn arg) = IAutoApp fc (applyEnv fn) arg
    applyEnv (INamedApp fc fn n arg)
        = INamedApp fc (applyEnv fn) n arg
    applyEnv tm = apply (expandNest tm) (addEnv (getFC tm) env)
