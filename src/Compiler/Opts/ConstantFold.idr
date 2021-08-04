module Compiler.Opts.ConstantFold

import Compiler.CompileExpr
import Core.Context
import Core.Context.Log
import Core.Primitives
import Core.Value
import Data.Vect

-- constant folding of primitive functions
-- if a primitive function is applied to only constant
-- then replace with the result
-- if there's only 1 constant argument to a commutative function
-- move the constant to the right. This simplifies Compiler.Opts.Identity
constFold : {vars : _} -> CExp vars -> CExp vars
constFold e@(CLocal _ _) = e
constFold e@(CRef fc x) = e
constFold (CLam fc x y) = CLam fc x $ constFold y
constFold (CLet fc x inlineOK y z) = CLet fc x inlineOK (constFold y) (constFold z)
constFold (CApp fc x xs) = CApp fc (constFold x) (constFold <$> xs)
constFold (CCon fc x y tag xs) = CCon fc x y tag $ constFold <$> xs
constFold e@(COp fc fn xs) = case the _ $ traverse toNF xs of
    Just nfs => maybe e (fromMaybe e . fromNF) $ getOp fn nfs
    Nothing => constRight fc fn xs
  where
    toNF : CExp vars -> Maybe (NF vars)
    toNF exp = case constFold exp of
        CPrimVal fc c => Just $ NPrimVal fc c
        _ => Nothing
    fromNF : NF vars -> Maybe (CExp vars)
    fromNF (NPrimVal fc c) = Just $ CPrimVal fc c
    fromNF _ = Nothing
    constRight : FC -> PrimFn ar -> Vect ar (CExp vars) -> CExp vars
    constRight fc (Add ty) [x@(CPrimVal _ _), y] = COp fc (Add ty) [constFold y, x]
    constRight fc (Mul ty) [x@(CPrimVal _ _), y] = COp fc (Mul ty) [constFold y, x]
    constRight _ _ _ = e
constFold (CExtPrim fc p xs) = CExtPrim fc p $ constFold <$> xs
constFold (CForce fc x y) = CForce fc x $ constFold y
constFold (CDelay fc x y) = CDelay fc x $ constFold y
constFold (CConCase fc sc xs x) = CConCase fc (constFold sc) (foldAlt <$> xs) (constFold <$> x)
  where
    foldAlt : CConAlt vars -> CConAlt vars
    foldAlt (MkConAlt n ci t xs e) = MkConAlt n ci t xs $ constFold e
constFold (CConstCase fc sc xs x) = CConstCase fc (constFold sc) (foldAlt <$> xs) (constFold <$> x)
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
