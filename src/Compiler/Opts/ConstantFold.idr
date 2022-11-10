module Compiler.Opts.ConstantFold

import Compiler.CompileExpr
import Core.Context
import Core.Context.Log
import Core.Primitives
import Core.Value
import Core.Name
import Data.List
import Data.Vect

findConstAlt : Constant -> List (CConstAlt vars) ->
               Maybe (CExp vars) -> Maybe (CExp vars)
findConstAlt c [] def = def
findConstAlt c (MkConstAlt c' exp :: alts) def = if c == c'
    then Just exp
    else findConstAlt c alts def

foldableOp : PrimFn ar -> Bool
foldableOp BelieveMe = False
foldableOp (Cast IntType _) = False
foldableOp (Cast _ IntType) = False
foldableOp (Cast from to)   = isJust (intKind from) && isJust (intKind to)
foldableOp _                = True


data Subst : List Name -> List Name -> Type where
  Nil  : Subst [] vars
  (::) : CExp vars -> Subst ds vars -> Subst (d :: ds) vars
  Wk   : SizeOf ws -> Subst ds vars -> Subst (ws ++ ds) (ws ++ vars)

initSubst : (vars : List Name) -> Subst vars vars
initSubst vars
  = rewrite sym $ appendNilRightNeutral vars in
    Wk (mkSizeOf vars) []


wk : SizeOf out -> Subst ds vars -> Subst (out ++ ds) (out ++ vars)
wk sout (Wk {ws, ds, vars} sws rho)
  = rewrite appendAssociative out ws ds in
    rewrite appendAssociative out ws vars in
    Wk (sout + sws) rho
wk ws rho = Wk ws rho

record WkCExp (vars : List Name) where
  constructor MkWkCExp
  {0 outer, supp : List Name}
  size : SizeOf outer
  0 prf : vars === outer ++ supp
  expr : CExp supp

Weaken WkCExp where
  weaken (MkWkCExp s Refl e) = MkWkCExp (suc s) Refl e

lookup : FC -> Var ds -> Subst ds vars -> CExp vars
lookup fc (MkVar p) rho = case go p rho of
    Left (MkVar p') => CLocal fc p'
    Right (MkWkCExp s Refl e) => weakenNs s e

  where

  go : {i : Nat} -> {0 ds, vars : _} -> (0 _ : IsVar n i ds) ->
       Subst ds vars -> Either (Var vars) (WkCExp vars)
  go First     (val :: rho) = Right (MkWkCExp zero Refl val)
  go (Later p) (val :: rho) = go p rho
  go p         (Wk ws  rho) = case sizedView ws of
    Z => go p rho
    S ws' => case i of
      Z => Left (MkVar First)
      S i' => bimap later weaken (go (dropLater p) (Wk ws' rho))

-- constant folding of primitive functions
-- if a primitive function is applied to only constant
-- then replace with the result
-- if there's only 1 constant argument to a commutative function
-- move the constant to the right. This simplifies Compiler.Opts.Identity
constFold : {vars' : _} ->
            Subst vars vars' ->
            CExp vars -> CExp vars'
constFold rho (CLocal fc p) = lookup fc (MkVar p) rho
constFold rho e@(CRef fc x) = CRef fc x
constFold rho (CLam fc x y)
  = CLam fc x $ constFold (wk (mkSizeOf [x]) rho) y
constFold rho (CLet fc x inlineOK y z) =
    let val = constFold rho y
     in case val of
        CPrimVal _ _ => if inlineOK
            then constFold (val :: rho) z
            else CLet fc x inlineOK val (constFold (wk (mkSizeOf [x]) rho) z)
        _ => CLet fc x inlineOK val (constFold (wk (mkSizeOf [x]) rho) z)
constFold rho (CApp fc (CRef fc2 n) [x]) =
  if n == NS typesNS (UN $ Basic "prim__integerToNat")
     then case constFold rho x of
            CPrimVal fc3 (BI v) =>
              if v >= 0 then CPrimVal fc3 (BI v) else CPrimVal fc3 (BI 0)
            v                   => CApp fc (CRef fc2 n) [v]
     else CApp fc (CRef fc2 n) [constFold rho x]
constFold rho (CApp fc x xs) = CApp fc (constFold rho x) (constFold rho <$> xs)
constFold rho (CCon fc x y tag xs) = CCon fc x y tag $ constFold rho <$> xs
constFold rho (COp {arity} fc fn xs) =
    let xs' = map (constFold rho) xs
        e = constRight fc fn xs'
     in fromMaybe e $ do
          guard (foldableOp fn)
          nfs <- traverse toNF xs'
          nf <- getOp fn nfs
          fromNF nf
  where
    toNF : CExp vars' -> Maybe (NF vars')
    -- Don't fold `Int` and `Double` because they have varying widths
    toNF (CPrimVal fc (I _)) = Nothing
    toNF (CPrimVal fc (Db _)) = Nothing
    -- Fold the rest
    toNF (CPrimVal fc c) = Just $ NPrimVal fc c
    toNF _ = Nothing

    fromNF : NF vars' -> Maybe (CExp vars')
    fromNF (NPrimVal fc c) = Just $ CPrimVal fc c
    fromNF _ = Nothing

    commutative : PrimType -> Bool
    commutative DoubleType = False
    commutative _ = True

    constRight : {ar : _} -> FC -> PrimFn ar ->
                 Vect ar (CExp vars') -> CExp vars'
    constRight fc (Add ty) [x@(CPrimVal _ _), y] =
        if commutative ty
            then COp fc (Add ty) [y, x]
            else COp fc (Add ty) [x, y]
    constRight fc (Mul ty) [x@(CPrimVal _ _), y] =
        if commutative ty
            then COp fc (Mul ty) [y, x]
            else COp fc (Mul ty) [x, y]
    constRight fc fn args = COp fc fn args

constFold rho (CExtPrim fc p xs) = CExtPrim fc p $ constFold rho <$> xs
constFold rho (CForce fc x y) = CForce fc x $ constFold rho y
constFold rho (CDelay fc x y) = CDelay fc x $ constFold rho y
constFold rho (CConCase fc sc xs x)
  = CConCase fc (constFold rho sc) (foldAlt <$> xs) (constFold rho <$> x)
  where
    foldAlt : CConAlt vars -> CConAlt vars'
    foldAlt (MkConAlt n ci t xs e)
      = MkConAlt n ci t xs $ constFold (wk (mkSizeOf xs) rho) e

constFold rho (CConstCase fc sc xs x) =
    let sc' = constFold rho sc
     in case sc' of
        CPrimVal _ val => case findConstAlt val xs x of
            Just exp => constFold rho exp
            Nothing => CConstCase fc (constFold rho sc) (foldAlt <$> xs) (constFold rho <$> x)
        _ => CConstCase fc (constFold rho sc) (foldAlt <$> xs) (constFold rho <$> x)
  where
    foldAlt : CConstAlt vars -> CConstAlt vars'
    foldAlt (MkConstAlt c e) = MkConstAlt c $ constFold rho e
constFold rho (CPrimVal fc v) = CPrimVal fc v
constFold rho (CErased fc) = CErased fc
constFold rho (CCrash fc err) = CCrash fc err

constFoldCDef : CDef -> Maybe CDef
constFoldCDef (MkFun args exp)
  = Just $ MkFun args $ constFold (initSubst args) exp
constFoldCDef _ = Nothing

export
constantFold : Ref Ctxt Defs => Name -> Core ()
constantFold fn = do
    defs <- get Ctxt
    Just (fnIdx, gdef) <- lookupCtxtExactI fn defs.gamma
        | Nothing => pure ()
    let Just cdef = gdef.compexpr
        | Nothing => pure ()
    let Just cdef' = constFoldCDef cdef
        | Nothing => pure ()
    log "compiler.const-fold" 50 $ "constant folding " ++ show !(getFullName fn)
                                 ++ "\n\told def: " ++ show cdef
                                 ++ "\n\tnew def: " ++ show cdef'
    setCompiled (Resolved fnIdx) cdef'
