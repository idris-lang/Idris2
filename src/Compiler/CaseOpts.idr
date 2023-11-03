module Compiler.CaseOpts

-- Case block related transformations

import Compiler.CompileExpr

import Core.CompileExpr
import Core.Context
import Core.FC
import Core.TT

import Data.SnocList
import Data.Vect

import Libraries.Data.Erased

%default covering

{-
Lifting out lambdas:

case t of
     C1 => \x1 => e1
     ...
     Cn => \xn = en

  where every branch begins with a lambda, can become:

\x => case t of
           C1 => e1[x/x1]
           ,,,
           Cn => en[x/xn]
-}

shiftUnder : {args : Scope} ->
             {idx : _} ->
             (0 p : IsVar n idx (vars ++ args :< x)) ->
             NVar n (vars :< x ++ args)
shiftUnder First = weakenNs (mkSizeOf args) (MkNVar First)
shiftUnder (Later p) = insertNVar (mkSizeOf args) (MkNVar p)

shiftVar : {local, args : Scope} ->
           {idx : _} ->
           (0 p : IsVar n idx ((vars ++ (args :< x)) ++ local)) ->
           NVar n ((vars :< x ++ args) ++ local)
shiftVar p
  = let s = mkSizeOf local in
    case locateIsVar s p of
      Left (MkErased p) => weakenNs s $ shiftUnder p
      Right (MkErased p) => embed (MkNVar p)

public export
0 Shiftable : Scoped -> Type
Shiftable tm = {0 vars, old : _} -> (local : Scope) -> {args : _} ->
               (new : Name) ->
               tm ((vars ++ args) :< old ++ local) ->
               tm ((vars :< new ++ args) ++ local)

mutual
  renameVar : IsVar x i ((vars :< old ++ args) ++ local) ->
              IsVar x i ((vars :< new ++ args) ++ local)
  renameVar = believe_me -- it's the same index, so just the identity at run time

  shiftBinder : Shiftable CExp
  shiftBinder local new (CLocal fc p)
      = case shiftVar p of
             MkNVar p' => CLocal fc (renameVar p')
  shiftBinder local new (CRef fc n) = CRef fc n
  shiftBinder local new (CLam fc n sc)
      = CLam fc n $ shiftBinder (local :< n) new sc
  shiftBinder local new (CLet fc n inlineOK val sc)
      = CLet fc n inlineOK (shiftBinder local new val)
                           $ shiftBinder (local :< n) new sc
  shiftBinder local new (CApp fc f args)
      = CApp fc (shiftBinder local new f) $ map (shiftBinder local new) args
  shiftBinder local new (CCon fc ci c tag args)
      = CCon fc ci c tag $ map (shiftBinder local new) args
  shiftBinder local new (COp fc op args) = COp fc op $ map (shiftBinder local new) args
  shiftBinder local new (CExtPrim fc p args)
      = CExtPrim fc p $ map (shiftBinder local new) args
  shiftBinder local new (CForce fc r arg) = CForce fc r $ shiftBinder local new arg
  shiftBinder local new (CDelay fc r arg) = CDelay fc r $ shiftBinder local new arg
  shiftBinder local new (CConCase fc sc alts def)
      = CConCase fc (shiftBinder local new sc)
                    (map (shiftBinderConAlt local new) alts)
                    (map (shiftBinder local new) def)
  shiftBinder local new (CConstCase fc sc alts def)
      = CConstCase fc (shiftBinder local new sc)
                      (map (shiftBinderConstAlt local new) alts)
                      (map (shiftBinder local new) def)
  shiftBinder local new (CPrimVal fc c) = CPrimVal fc c
  shiftBinder local new (CErased fc) = CErased fc
  shiftBinder local new (CCrash fc msg) = CCrash fc msg

  shiftBinderConAlt : Shiftable CConAlt
  shiftBinderConAlt local new (MkConAlt n ci t args' sc)
      = let sc' : CExp ((vars ++ args :< old) ++ (local ++ args'))
                = rewrite  (appendAssociative (vars ++ args :< old) local args') in sc in
        MkConAlt n ci t args' $
           rewrite sym (appendAssociative (vars :< new ++ args) local args')
             in shiftBinder (local ++ args') new sc'

  shiftBinderConstAlt : Shiftable CConstAlt
  shiftBinderConstAlt local new (MkConstAlt c sc) = MkConstAlt c $ shiftBinder local new sc

-- If there's a lambda inside a case, move the variable so that it's bound
-- outside the case block so that we can bind it just once outside the block
liftOutLambda : {args : _} ->
                (new : Name) ->
                CExp (vars ++ args :< old) ->
                CExp (vars :< new ++ args)
liftOutLambda = shiftBinder [<]

-- If all the alternatives start with a lambda, we can have a single lambda
-- binding outside
tryLiftOut : (new : Name) ->
             List (CConAlt vars) ->
             Maybe (List (CConAlt (vars :< new)))
tryLiftOut new [] = Just []
tryLiftOut new (MkConAlt n ci t args (CLam fc x sc) :: as)
    = do as' <- tryLiftOut new as
         let sc' = liftOutLambda new sc
         pure (MkConAlt n ci t args sc' :: as')
tryLiftOut _ _ = Nothing

tryLiftOutConst : (new : Name) ->
                  List (CConstAlt vars) ->
                  Maybe (List (CConstAlt (vars :< new)))
tryLiftOutConst new [] = Just []
tryLiftOutConst new (MkConstAlt c (CLam fc x sc) :: as)
    = do as' <- tryLiftOutConst new as
         let sc' = liftOutLambda {args = [<]} new sc
         pure (MkConstAlt c sc' :: as')
tryLiftOutConst _ _ = Nothing

tryLiftDef : (new : Name) ->
             Maybe (CExp vars) ->
             Maybe (Maybe (CExp (vars :< new)))
tryLiftDef new Nothing = Just Nothing
tryLiftDef new (Just (CLam fc x sc))
   = let sc' = liftOutLambda {args = [<]} new sc in
         pure (Just sc')
tryLiftDef _ _ = Nothing

allLams : List (CConAlt vars) -> Bool
allLams [] = True
allLams (MkConAlt n ci t args (CLam _ _ _) :: as)
   = allLams as
allLams _ = False

allLamsConst : List (CConstAlt vars) -> Bool
allLamsConst [] = True
allLamsConst (MkConstAlt c (CLam _ _ _) :: as)
   = allLamsConst as
allLamsConst _ = False

-- label for next name for a lambda. These probably don't need really to be
-- unique, since we've proved things about the de Bruijn index, but it's easier
-- to see what's going on if they are.
data NextName : Type where

getName : {auto n : Ref NextName Int} ->
          Core Name
getName
    = do n <- get NextName
         put NextName (n + 1)
         pure (MN "clam" n)

-- The transformation itself
mutual
  caseLam : {auto n : Ref NextName Int} ->
            CExp vars -> Core (CExp vars)
  -- Interesting cases first: look for case blocks where every branch is a
  -- lambda
  caseLam (CConCase fc sc alts def)
      = if allLams alts && defLam def
           then do var <- getName
                   -- These will work if 'allLams' and 'defLam' are consistent.
                   -- We only do that boolean check because it saves us doing
                   -- unnecessary work (say, if the last one we try fails)
                   let Just newAlts = tryLiftOut var alts
                            | Nothing => throw (InternalError "Can't happen caseLam 1")
                   let Just newDef = tryLiftDef var def
                            | Nothing => throw (InternalError "Can't happen caseLam 2")
                   newAlts' <- traverse caseLamConAlt newAlts
                   newDef' <- traverseOpt caseLam newDef
                   -- Q: Should we go around again?
                   pure (CLam fc var (CConCase fc (weaken sc) newAlts' newDef'))
           else do sc' <- caseLam sc
                   alts' <- traverse caseLamConAlt alts
                   def' <- traverseOpt caseLam def
                   pure (CConCase fc sc' alts' def')
    where
      defLam : Maybe (CExp vars) -> Bool
      defLam Nothing = True
      defLam (Just (CLam _ _ _)) = True
      defLam _ = False
  -- Next case is pretty much as above. There's a boring amount of repetition
  -- here because ConstCase is just a little bit different.
  caseLam (CConstCase fc sc alts def)
      = if allLamsConst alts && defLam def
           then do var <- getName
                   -- These will work if 'allLams' and 'defLam' are consistent.
                   -- We only do that boolean check because it saves us doing
                   -- unnecessary work (say, if the last one we try fails)
                   let Just newAlts = tryLiftOutConst var alts
                            | Nothing => throw (InternalError "Can't happen caseLam 1")
                   let Just newDef = tryLiftDef var def
                            | Nothing => throw (InternalError "Can't happen caseLam 2")
                   newAlts' <- traverse caseLamConstAlt newAlts
                   newDef' <- traverseOpt caseLam newDef
                   pure (CLam fc var (CConstCase fc (weaken sc) newAlts' newDef'))
           else do sc' <- caseLam sc
                   alts' <- traverse caseLamConstAlt alts
                   def' <- traverseOpt caseLam def
                   pure (CConstCase fc sc' alts' def')
    where
      defLam : Maybe (CExp vars) -> Bool
      defLam Nothing = True
      defLam (Just (CLam _ _ _)) = True
      defLam _ = False
  -- Structural recursive cases
  caseLam (CLam fc x sc)
      = CLam fc x <$> caseLam sc
  caseLam (CLet fc x inl val sc)
      = CLet fc x inl <$> caseLam val <*> caseLam sc
  caseLam (CApp fc f args)
      = CApp fc <$> caseLam f <*> traverse caseLam args
  caseLam (CCon fc n ci t args)
      = CCon fc n ci t <$> traverse caseLam args
  caseLam (COp fc op args)
      = COp fc op <$> traverseVect caseLam args
  caseLam (CExtPrim fc p args)
      = CExtPrim fc p <$> traverse caseLam args
  caseLam (CForce fc r x)
      = CForce fc r <$> caseLam x
  caseLam (CDelay fc r x)
      = CDelay fc r <$> caseLam x
  -- All the others, no recursive case so just return the input
  caseLam x = pure x

  caseLamConAlt : {auto n : Ref NextName Int} ->
                  CConAlt vars -> Core (CConAlt vars)
  caseLamConAlt (MkConAlt n ci tag args sc)
      = MkConAlt n ci tag args <$> caseLam sc

  caseLamConstAlt : {auto n : Ref NextName Int} ->
                    CConstAlt vars -> Core (CConstAlt vars)
  caseLamConstAlt (MkConstAlt c sc) = MkConstAlt c <$> caseLam sc

export
caseLamDef : {auto c : Ref Ctxt Defs} ->
             Name -> Core ()
caseLamDef n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs) | Nothing => pure ()
         let Just cexpr =  compexpr def             | Nothing => pure ()
         setCompiled n !(doCaseLam cexpr)
  where
    doCaseLam : CDef -> Core CDef
    doCaseLam (MkFun args def)
        = do n <- newRef NextName 0
             pure $ MkFun args !(caseLam def)
    doCaseLam d = pure d

{-

Case of case:

case (case x of C1 => E1
                C2 => E2
                _ => Ed
                ...) of
     D1 => F1
     D2 => F2
     ...
     _ => Fd

can become

case x of
     C1 => case E1 of
                D1 => F1
                D2 => F2
                ...
                _ => Fd
     C2 => case E2 of
                D1 => F1
                D2 => F2
                ...
                _ => Fd
    _ => case Ed of
              D1 => F1
              D2 => F2
              ...
              _ => Fd

to minimise risk of duplication, do this only when E1, E2 are all
constructor headed, or there's only one branch (for now)

-}

doCaseOfCase : FC ->
               (x : CExp vars) ->
               (xalts : List (CConAlt vars)) ->
               (xdef : Maybe (CExp vars)) ->
               (alts : List (CConAlt vars)) ->
               (def : Maybe (CExp vars)) ->
               CExp vars
doCaseOfCase fc x xalts xdef alts def
    = CConCase fc x (map updateAlt xalts) (map updateDef xdef)
  where
    updateAlt : CConAlt vars -> CConAlt vars
    updateAlt (MkConAlt n ci t args sc)
        = MkConAlt n ci t args $
              CConCase fc sc
                       (map (weakenNs (mkSizeOf args)) alts)
                       (map (weakenNs (mkSizeOf args)) def)

    updateDef : CExp vars -> CExp vars
    updateDef sc = CConCase fc sc alts def

doCaseOfConstCase : FC ->
                    (x : CExp vars) ->
                    (xalts : List (CConstAlt vars)) ->
                    (xdef : Maybe (CExp vars)) ->
                    (alts : List (CConstAlt vars)) ->
                    (def : Maybe (CExp vars)) ->
                    CExp vars
doCaseOfConstCase fc x xalts xdef alts def
    = CConstCase fc x (map updateAlt xalts) (map updateDef xdef)
  where
    updateAlt : CConstAlt vars -> CConstAlt vars
    updateAlt (MkConstAlt c sc)
        = MkConstAlt c $
              CConstCase fc sc alts def

    updateDef : CExp vars -> CExp vars
    updateDef sc = CConstCase fc sc alts def

tryCaseOfCase : CExp vars -> Maybe (CExp vars)
tryCaseOfCase (CConCase fc (CConCase fc' x xalts xdef) alts def)
    = if canCaseOfCase xalts xdef
         then Just (doCaseOfCase fc' x xalts xdef alts def)
         else Nothing
  where
    isCon : CExp vars -> Bool
    isCon (CCon {}) = True
    isCon _ = False

    conCase : CConAlt vars -> Bool
    conCase (MkConAlt _ _ _ _ (CCon {})) = True
    conCase _ = False

    canCaseOfCase : List (CConAlt vars) -> Maybe (CExp vars) -> Bool
    canCaseOfCase [] _ = True
    canCaseOfCase [x] Nothing = True
    canCaseOfCase xs mdef = all conCase xs && maybe True isCon mdef
tryCaseOfCase (CConstCase fc (CConstCase fc' x xalts xdef) alts def)
    = if canCaseOfCase xalts xdef
         then Just (doCaseOfConstCase fc' x xalts xdef alts def)
         else Nothing
  where
    isConst : CExp vars -> Bool
    isConst (CPrimVal {}) = True
    isConst def = False

    constCase : CConstAlt vars -> Bool
    constCase (MkConstAlt _ (CPrimVal {})) = True
    constCase _ = False

    canCaseOfCase : List (CConstAlt vars) -> Maybe (CExp vars) -> Bool
    canCaseOfCase [] _ = True
    canCaseOfCase [x] Nothing = True
    canCaseOfCase xs mdef = all constCase xs && maybe True isConst mdef
tryCaseOfCase _ = Nothing

export
caseOfCase : CExp vars -> CExp vars
caseOfCase tm = go 5 tm
  where
    go : Nat -> CExp vars -> CExp vars
    go Z tm = tm
    go (S k) tm = maybe tm (go k) (tryCaseOfCase tm)
