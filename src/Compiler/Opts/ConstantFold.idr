module Compiler.Opts.ConstantFold

import Compiler.CompileExpr
import Core.Context
import Core.Context.Log
import Core.Primitives
import Core.Value
import Data.List
import Data.Vect

find : FC -> SizeOf outer -> CExp inner ->
       Var (outer ++ [x] ++ inner) -> CExp (outer ++ inner)
find fc out val var = case removeVar out var of
  Nothing => weakenNs out val
  Just (MkVar p) => CLocal fc p

namespace Inline
  mutual
    inlineLetEnv : SizeOf outer -> CExp inner -> CExp (outer ++ [x] ++ inner) -> CExp (outer ++ inner)
    inlineLetEnv out val (CLocal fc p) = find fc out val (MkVar p)
    inlineLetEnv out val (CRef fc y) = CRef fc y
    inlineLetEnv out val (CLam fc y z) = CLam fc y $ inlineLetEnv (suc out) val z
    inlineLetEnv out val (CLet fc y inlineOK z w) = CLet fc y inlineOK (inlineLetEnv out val z) (inlineLetEnv (suc out) val w)
    inlineLetEnv out val (CApp fc y xs) = CApp fc (inlineLetEnv out val y) (inlineLetEnv out val <$> xs)
    inlineLetEnv out val (CCon fc y z tag xs) = CCon fc y z tag $ inlineLetEnv out val <$> xs
    inlineLetEnv out val (COp fc y xs) = COp fc y $ inlineLetEnv out val <$> xs
    inlineLetEnv out val (CExtPrim fc p xs) = CExtPrim fc p $ inlineLetEnv out val <$> xs
    inlineLetEnv out val (CForce fc y z) = CForce fc y $ inlineLetEnv out val z
    inlineLetEnv out val (CDelay fc y z) = CDelay fc y $ inlineLetEnv out val z
    inlineLetEnv out val (CConCase fc sc xs y) = CConCase fc (inlineLetEnv out val sc) (inlineLetConAlt out val <$> xs) (inlineLetEnv out val <$> y)
    inlineLetEnv out val (CConstCase fc sc xs y) = CConstCase fc (inlineLetEnv out val sc) (inlineLetConstAlt out val <$> xs) (inlineLetEnv out val <$> y)
    inlineLetEnv out val (CPrimVal fc y) = CPrimVal fc y
    inlineLetEnv out val (CErased fc) = CErased fc
    inlineLetEnv out val (CCrash fc y) = CCrash fc y

    inlineLetConAlt : SizeOf outer -> CExp inner -> CConAlt (outer ++ [x] ++ inner) -> CConAlt (outer ++ inner)
    inlineLetConAlt out val (MkConAlt y z tag args w) = MkConAlt y z tag args $
        replace {p=CExp} (sym $ appendAssociative args outer inner) $
        inlineLetEnv (mkSizeOf args + out) val $
        replace {p=CExp} (appendAssociative args outer ([x] ++ inner)) w

    inlineLetConstAlt : SizeOf outer -> CExp inner -> CConstAlt (outer ++ [x] ++ inner) -> CConstAlt (outer ++ inner)
    inlineLetConstAlt out val (MkConstAlt c e) = MkConstAlt c $ inlineLetEnv out val e

  export
  inlineLet : CExp vars -> CExp (x :: vars) -> CExp vars
  inlineLet val exp = inlineLetEnv zero val exp

findConstAlt : Constant -> List (CConstAlt vars) -> Maybe (CExp vars) -> Maybe (CExp vars)
findConstAlt c [] def = def
findConstAlt c (MkConstAlt c' exp :: alts) def = if c == c'
    then Just exp
    else findConstAlt c alts def

foldableOp : PrimFn ar -> Bool
foldableOp BelieveMe = False
foldableOp (Cast from to) = fromMaybe False [| intKind from `smaller` intKind to |]
  where
    smaller : IntKind -> IntKind -> Bool
    smaller (Signed x) (Signed y) = x <= y
    smaller (Unsigned x) (Unsigned y) = x <= y
    smaller (Signed x) (Unsigned y) = x < P y
    smaller (Unsigned x) (Signed y) = P x < y
foldableOp _ = True

-- constant folding of primitive functions
-- if a primitive function is applied to only constant
-- then replace with the result
-- if there's only 1 constant argument to a commutative function
-- move the constant to the right. This simplifies Compiler.Opts.Identity
constFold : {vars : _} -> CExp vars -> CExp vars
constFold e@(CLocal _ _) = e
constFold e@(CRef fc x) = e
constFold (CLam fc x y) = CLam fc x $ constFold y
constFold (CLet fc x inlineOK y z) =
    let val = constFold y
     in case val of
        CPrimVal _ _ => if inlineOK
            then constFold $ inlineLet val z
            else CLet fc x inlineOK val (constFold z)
        _ => CLet fc x inlineOK val (constFold z)
constFold (CApp fc x xs) = CApp fc (constFold x) (constFold <$> xs)
constFold (CCon fc x y tag xs) = CCon fc x y tag $ constFold <$> xs
constFold (COp {arity} fc fn xs) =
    let xs' : Vect arity (CExp vars)
        xs' = map constFold xs
        e : CExp vars
        e = constRight fc fn xs'
     in if foldableOp fn
        then case the (Maybe (Vect arity (NF vars))) $ Prelude.traverse toNF xs' of
                Nothing => e
                Just nfs => case getOp fn nfs of
                    Just nf => fromMaybe e $ fromNF nf
                    Nothing => e
        else e
  where
    toNF : CExp vars -> Maybe (NF vars)
    toNF (CPrimVal fc (I _)) = Nothing -- don't fold `Int` because it has varying widths
    toNF (CPrimVal fc (Db _)) = Nothing
    toNF (CPrimVal fc c) = Just $ NPrimVal fc c
    toNF _ = Nothing

    fromNF : NF vars -> Maybe (CExp vars)
    fromNF (NPrimVal fc c) = Just $ CPrimVal fc c
    fromNF _ = Nothing

    commutative : Constant -> Bool
    commutative DoubleType = False
    commutative _ = True

    constRight : {ar : _} -> FC -> PrimFn ar -> Vect ar (CExp vars) -> CExp vars
    constRight fc (Add ty) [x@(CPrimVal _ _), y] =
        if commutative ty
            then COp fc (Add ty) [y, x]
            else COp fc (Add ty) [x, y]
    constRight fc (Mul ty) [x@(CPrimVal _ _), y] =
        if commutative ty
            then COp fc (Mul ty) [y, x]
            else COp fc (Mul ty) [x, y]
    constRight fc fn args = COp fc fn args

constFold (CExtPrim fc p xs) = CExtPrim fc p $ constFold <$> xs
constFold (CForce fc x y) = CForce fc x $ constFold y
constFold (CDelay fc x y) = CDelay fc x $ constFold y
constFold (CConCase fc sc xs x) = CConCase fc (constFold sc) (foldAlt <$> xs) (constFold <$> x)
  where
    foldAlt : CConAlt vars -> CConAlt vars
    foldAlt (MkConAlt n ci t xs e) = MkConAlt n ci t xs $ constFold e
constFold (CConstCase fc sc xs x) =
    let sc' = constFold sc
     in case sc' of
        CPrimVal _ val => case findConstAlt val xs x of
            Just exp => constFold exp
            Nothing => CConstCase fc (constFold sc) (foldAlt <$> xs) (constFold <$> x)
        _ => CConstCase fc (constFold sc) (foldAlt <$> xs) (constFold <$> x)
  where
    foldAlt : CConstAlt vars -> CConstAlt vars
    foldAlt (MkConstAlt c e) = MkConstAlt c $ constFold e
constFold e@(CPrimVal _ _) = e
constFold e@(CErased _) = e
constFold e@(CCrash _ _) = e


constFoldCDef : CDef -> Maybe CDef
constFoldCDef (MkFun args exp) = Just $ MkFun args $ constFold exp
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
