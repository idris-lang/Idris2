module Compiler.Opts.Identity

import Core.CompileExpr
import Core.Context.Log

import Data.Vect
import Data.SnocList

import Libraries.Data.List.SizeOf

makeArgz : (args : List Name) -> List (Var (Scope.ext vars args))
makeArgz args
  = embedFishily @{ListFreelyEmbeddable} $ Var.List.allVars args

parameters (fn1 : Name) (idIdx : Nat)
  mutual
    -- special case for matching on 'Nat'-shaped things
    isUnsucc : Var vars -> CExp vars -> Maybe (Constant, Var (Scope.bind vars x))
    isUnsucc var (COp _ (Sub _) [CLocal _ p, CPrimVal _ c]) =
        if var == MkVar p
            then Just (c, first)
            else Nothing
    isUnsucc _ _ = Nothing

    unsuccIdentity : Constant -> Var vars -> CExp vars -> Bool
    unsuccIdentity c1 var (COp _ (Add _) [exp, CPrimVal _ c2]) = c1 == c2 && cexpIdentity var Nothing Nothing exp
    unsuccIdentity _ _ _ = False

    -- does the CExp evaluate to the var, the constructor or the constant?
    cexpIdentity : Var vars -> Maybe (Name, List (Var vars)) -> Maybe Constant -> CExp vars -> Bool
    cexpIdentity var _ _ (CLocal fc p) = var == MkVar p
    cexpIdentity var _ _ (CRef {}) = False
    cexpIdentity var _ _ (CLam {}) = False
    cexpIdentity var con const (CLet _ _ NotInline val sc) = False
    cexpIdentity var con const (CLet _ _ _ val sc) = (case isUnsucc var val of
        Just (c, var') => unsuccIdentity c var' sc
        Nothing => False)
        || cexpIdentity
            (weaken var)
            (map (map (map weaken)) con)
            const
            sc
    cexpIdentity var con const (CApp _ (CRef _ fn2) as) = -- special case for self-recursive functions
        fn1 == fn2 &&
        case getAt idIdx as of
            Just exp => cexpIdentity var con const exp
            Nothing => False
    cexpIdentity _ _ _ (CApp {}) = False
    cexpIdentity var (Just (con1, as1)) const (CCon _ con2 _ _ as2) =
        con1 == con2
        && eqArgs as1 as2
      where
        eqArgs : List (Var vars) -> List (CExp vars) -> Bool
        eqArgs [] [] = True
        eqArgs (v :: vs) (a :: as) = cexpIdentity v Nothing Nothing a && eqArgs vs as
        eqArgs _ _ = False
    cexpIdentity var Nothing const (CCon {}) = False
    -- special case for integerToNat, see unsuccIdentity for a easier to read
    -- version that works when the let hasn't been inlined.
    -- integerToNat : (x : Integer) -> {auto 0 _ : (x >= 0) === True} -> Nat
    -- integerToNat x = case x of
    --                       0 => Z
    --                       _ => S $ integerToNat (x - 1)
    cexpIdentity var _ _ (COp _ (Add _) [a1, a2]) = case a2 of
        CPrimVal _ c1 => case a1 of
            CApp _ (CRef _ fn2) as =>
                fn1 == fn2
                && (case getAt idIdx as of
                    Just (COp _ (Sub _) [a3, (CPrimVal _ c2)]) =>
                        c1 == c2 && cexpIdentity var Nothing Nothing a3
                    _ => False)
            _ => False
        _ => False
    cexpIdentity var _ _ (COp {}) = False
    cexpIdentity var _ _ (CExtPrim {}) = False
    cexpIdentity var _ _ (CForce {}) = False
    cexpIdentity var _ _ (CDelay {}) = False
    cexpIdentity var con const (CConCase _ sc xs x) =
        cexpIdentity var Nothing Nothing sc
        && all altEq xs
        && maybeVarEq var con const x
      where

        altEq : CConAlt vars -> Bool
        altEq (MkConAlt y _ _ args exp) =
            cexpIdentity
                (weakensN (mkSizeOf args) var)
                (Just (y, makeArgz args))
                const
                exp
    cexpIdentity var con const (CConstCase fc sc xs x) =
        cexpIdentity var Nothing Nothing sc
        && all altEq xs
        && maybeVarEq var con const x
    where
        altEq : CConstAlt vars -> Bool
        altEq (MkConstAlt c exp) = cexpIdentity var con (Just c) exp
    cexpIdentity _ _ (Just c1) (CPrimVal _ c2) = c1 == c2
    cexpIdentity _ _ Nothing (CPrimVal {}) = False
    cexpIdentity _ _ _ (CErased _) = False
    cexpIdentity _ _ _ (CCrash {}) = False

    -- fused `all (cexpIdentity var con const)`
    maybeVarEq : Var vars -> Maybe (Name, List (Var vars)) -> Maybe Constant -> Maybe (CExp vars) -> Bool
    maybeVarEq _ _ _ Nothing = True
    maybeVarEq var con const (Just exp) = cexpIdentity var con const exp

checkIdentity : (fullName : Name) -> Scopeable (Var vars) -> CExp vars -> Nat -> Maybe Nat
checkIdentity _ [<] _ _ = Nothing
checkIdentity fn (vs :< v) exp idx = if cexpIdentity fn idx v Nothing Nothing exp
    then Just idx
    else checkIdentity fn vs exp (S idx)

calcIdentity : (fullName : Name) -> CDef -> Maybe Nat
calcIdentity fn (MkFun args exp) = checkIdentity fn (Var.SnocList.allVars args) exp Z
calcIdentity _ _ = Nothing

getArg : FC -> Nat -> (args : Scope) -> Maybe (CExp args)
getArg _ _ [<] = Nothing
getArg fc Z (_ :< a) = Just $ CLocal fc First
getArg fc (S k) (as :< _) = weaken <$> getArg fc k as

idCDef : Nat -> CDef -> Maybe CDef
idCDef idx (MkFun args exp) = MkFun args <$> getArg (getFC exp) idx args
idCDef _ def = Just def

export
rewriteIdentityFlag : Ref Ctxt Defs => Name -> Core ()
rewriteIdentityFlag fn = do
    defs <- get Ctxt
    Just (fnIdx, gdef) <- lookupCtxtExactI fn defs.gamma
        | Nothing => pure ()
    let Just flg@(Identity idx) = find isId gdef.flags
        | _ => pure ()
    log "compiler.identity" 5 $ "found identity flag for: "
                              ++ show !(getFullName fn) ++ ", " ++ show idx
                              ++ "\n\told def: " ++ show gdef.compexpr
    let Just cdef = the _ $ gdef.compexpr >>= idCDef idx
        | Nothing => pure ()
    log "compiler.identity" 5 $ "\tnew def: " ++ show cdef
    unsetFlag EmptyFC (Resolved fnIdx) flg -- other optimisations might mess with argument counts
    setFlag EmptyFC (Resolved fnIdx) Inline
    setCompiled (Resolved fnIdx) cdef
  where
    isId : DefFlag -> Bool
    isId (Identity _) = True
    isId _ = False

export
setIdentity : Ref Ctxt Defs => Name -> Core ()
setIdentity fn = do
    defs <- get Ctxt
    Just (fnIdx, gdef) <- lookupCtxtExactI fn defs.gamma
        | Nothing => pure ()
    let Just idx = the _ $ gdef.compexpr >>= calcIdentity fn
        | Nothing => pure ()
    setFlag EmptyFC (Resolved fnIdx) (Identity idx)
    rewriteIdentityFlag (Resolved fnIdx)
