module TTImp.Reflect

import Core.Context
import Core.Env
import Core.Normalise
import Core.Reflect
import Core.TT
import Core.Value

import TTImp.TTImp

%default covering

export
Reify BindMode where
  reify defs val@(NDCon _ n _ _ args)
      = case (!(full (gamma defs) n), args) of
             (NS _ (UN "PI"), [(_, c)])
                 => do c' <- reify defs !(evalClosure defs c)
                       pure (PI c')
             (NS _ (UN "PATTERN"), _) => pure PATTERN
             (NS _ (UN "NONE"), _) => pure NONE
             _ => cantReify val "BindMode"
  reify deva val = cantReify val "BindMode"

export
Reflect BindMode where
  reflect fc defs lhs env (PI c)
      = do c' <- reflect fc defs lhs env c
           appCon fc defs (reflectionttimp "PI") [c']
  reflect fc defs lhs env PATTERN
      = getCon fc defs (reflectionttimp "PATTERN")
  reflect fc defs lhs env NONE
      = getCon fc defs (reflectionttimp "NONE")

export
Reify UseSide where
  reify defs val@(NDCon _ n _ _ args)
      = case (!(full (gamma defs) n), args) of
             (NS _ (UN "UseLeft"), _) => pure UseLeft
             (NS _ (UN "UseRight"), _) => pure UseRight
             _ => cantReify val "UseSide"
  reify defs val = cantReify val "UseSide"

export
Reflect UseSide where
  reflect fc defs lhs env UseLeft
      = getCon fc defs (reflectionttimp "UseLeft")
  reflect fc defs lhs env UseRight
      = getCon fc defs (reflectionttimp "UseRight")

export
Reify DotReason where
  reify defs val@(NDCon _ n _ _ args)
      = case (!(full (gamma defs) n), args) of
             (NS _ (UN "NonLinearVar"), _) => pure NonLinearVar
             (NS _ (UN "VarApplied"), _) => pure VarApplied
             (NS _ (UN "NotConstructor"), _) => pure NotConstructor
             (NS _ (UN "ErasedArg"), _) => pure ErasedArg
             (NS _ (UN "UserDotted"), _) => pure UserDotted
             (NS _ (UN "UnknownDot"), _) => pure UnknownDot
             (NS _ (UN "UnderAppliedCon"), _) => pure UnderAppliedCon
             _ => cantReify val "DotReason"
  reify defs val = cantReify val "DotReason"

export
Reflect DotReason where
  reflect fc defs lhs env NonLinearVar
      = getCon fc defs (reflectionttimp "NonLinearVar")
  reflect fc defs lhs env VarApplied
      = getCon fc defs (reflectionttimp "VarApplied")
  reflect fc defs lhs env NotConstructor
      = getCon fc defs (reflectionttimp "NotConstructor")
  reflect fc defs lhs env ErasedArg
      = getCon fc defs (reflectionttimp "ErasedArg")
  reflect fc defs lhs env UserDotted
      = getCon fc defs (reflectionttimp "UserDotted")
  reflect fc defs lhs env UnknownDot
      = getCon fc defs (reflectionttimp "UnknownDot")
  reflect fc defs lhs env UnderAppliedCon
      = getCon fc defs (reflectionttimp "UnderAppliedCon")


mutual
  export
  Reify RawImp where
    reify defs val@(NDCon _ n _ _ args)
        = case (!(full (gamma defs) n), map snd args) of
               (NS _ (UN "IVar"), [fc, n])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          n' <- reify defs !(evalClosure defs n)
                          pure (IVar fc' n')
               (NS _ (UN "IPi"), [fc, c, p, mn, aty, rty])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          c' <- reify defs !(evalClosure defs c)
                          p' <- reify defs !(evalClosure defs p)
                          mn' <- reify defs !(evalClosure defs mn)
                          aty' <- reify defs !(evalClosure defs aty)
                          rty' <- reify defs !(evalClosure defs rty)
                          pure (IPi fc' c' p' mn' aty' rty')
               (NS _ (UN "ILam"), [fc, c, p, mn, aty, lty])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          c' <- reify defs !(evalClosure defs c)
                          p' <- reify defs !(evalClosure defs p)
                          mn' <- reify defs !(evalClosure defs mn)
                          aty' <- reify defs !(evalClosure defs aty)
                          lty' <- reify defs !(evalClosure defs lty)
                          pure (ILam fc' c' p' mn' aty' lty')
               (NS _ (UN "ILet"), [fc, lhsFC, c, n, ty, val, sc])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          lhsFC' <- reify defs !(evalClosure defs lhsFC)
                          c' <- reify defs !(evalClosure defs c)
                          n' <- reify defs !(evalClosure defs n)
                          ty' <- reify defs !(evalClosure defs ty)
                          val' <- reify defs !(evalClosure defs val)
                          sc' <- reify defs !(evalClosure defs sc)
                          pure (ILet fc' lhsFC' c' n' ty' val' sc')
               (NS _ (UN "ICase"), [fc, sc, ty, cs])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          sc' <- reify defs !(evalClosure defs sc)
                          ty' <- reify defs !(evalClosure defs ty)
                          cs' <- reify defs !(evalClosure defs cs)
                          pure (ICase fc' sc' ty' cs')
               (NS _ (UN "ILocal"), [fc, ds, sc])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          ds' <- reify defs !(evalClosure defs ds)
                          sc' <- reify defs !(evalClosure defs sc)
                          pure (ILocal fc' ds' sc')
               (NS _ (UN "IUpdate"), [fc, ds, sc])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          ds' <- reify defs !(evalClosure defs ds)
                          sc' <- reify defs !(evalClosure defs sc)
                          pure (IUpdate fc' ds' sc')
               (NS _ (UN "IApp"), [fc, f, a])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          f' <- reify defs !(evalClosure defs f)
                          a' <- reify defs !(evalClosure defs a)
                          pure (IApp fc' f' a')
               (NS _ (UN "INamedApp"), [fc, f, m, a])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          f' <- reify defs !(evalClosure defs f)
                          m' <- reify defs !(evalClosure defs m)
                          a' <- reify defs !(evalClosure defs a)
                          pure (INamedApp fc' f' m' a')
               (NS _ (UN "IAutoApp"), [fc, f, a])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          f' <- reify defs !(evalClosure defs f)
                          a' <- reify defs !(evalClosure defs a)
                          pure (IAutoApp fc' f' a')
               (NS _ (UN "IWithApp"), [fc, f, a])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          f' <- reify defs !(evalClosure defs f)
                          a' <- reify defs !(evalClosure defs a)
                          pure (IWithApp fc' f' a')
               (NS _ (UN "ISearch"), [fc, d])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          d' <- reify defs !(evalClosure defs d)
                          pure (ISearch fc' d')
               (NS _ (UN "IAlternative"), [fc, t, as])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          t' <- reify defs !(evalClosure defs t)
                          as' <- reify defs !(evalClosure defs as)
                          pure (IAlternative fc' t' as')
               (NS _ (UN "IRewrite"), [fc, t, sc])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          t' <- reify defs !(evalClosure defs t)
                          sc' <- reify defs !(evalClosure defs sc)
                          pure (IRewrite fc' t' sc')
               (NS _ (UN "IBindHere"), [fc, t, sc])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          t' <- reify defs !(evalClosure defs t)
                          sc' <- reify defs !(evalClosure defs sc)
                          pure (IBindHere fc' t' sc')
               (NS _ (UN "IBindVar"), [fc, n])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          n' <- reify defs !(evalClosure defs n)
                          pure (IBindVar fc' n')
               (NS _ (UN "IAs"), [fc, nameFC, s, n, t])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          nameFC' <- reify defs !(evalClosure defs nameFC)
                          s' <- reify defs !(evalClosure defs s)
                          n' <- reify defs !(evalClosure defs n)
                          t' <- reify defs !(evalClosure defs t)
                          pure (IAs fc' nameFC' s' n' t')
               (NS _ (UN "IMustUnify"), [fc, r, t])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          r' <- reify defs !(evalClosure defs r)
                          t' <- reify defs !(evalClosure defs t)
                          pure (IMustUnify fc' r' t')
               (NS _ (UN "IDelayed"), [fc, r, t])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          r' <- reify defs !(evalClosure defs r)
                          t' <- reify defs !(evalClosure defs t)
                          pure (IDelayed fc' r' t')
               (NS _ (UN "IDelay"), [fc, t])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          t' <- reify defs !(evalClosure defs t)
                          pure (IDelay fc' t')
               (NS _ (UN "IForce"), [fc, t])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          t' <- reify defs !(evalClosure defs t)
                          pure (IForce fc' t')
               (NS _ (UN "IQuote"), [fc, t])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          t' <- reify defs !(evalClosure defs t)
                          pure (IQuote fc' t')
               (NS _ (UN "IQuoteName"), [fc, t])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          t' <- reify defs !(evalClosure defs t)
                          pure (IQuoteName fc' t')
               (NS _ (UN "IQuoteDecl"), [fc, t])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          t' <- reify defs !(evalClosure defs t)
                          pure (IQuoteDecl fc' t')
               (NS _ (UN "IUnquote"), [fc, t])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          t' <- reify defs !(evalClosure defs t)
                          pure (IUnquote fc' t')
               (NS _ (UN "IPrimVal"), [fc, t])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          t' <- reify defs !(evalClosure defs t)
                          pure (IPrimVal fc' t')
               (NS _ (UN "IType"), [fc])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          pure (IType fc')
               (NS _ (UN "IHole"), [fc, n])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          n' <- reify defs !(evalClosure defs n)
                          pure (IHole fc' n')
               (NS _ (UN "Implicit"), [fc, n])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          n' <- reify defs !(evalClosure defs n)
                          pure (Implicit fc' n')
               (NS _ (UN "IWithUnambigNames"), [fc, ns, t])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          ns' <- reify defs !(evalClosure defs ns)
                          t' <- reify defs !(evalClosure defs t)
                          pure (IWithUnambigNames fc' ns' t')
               _ => cantReify val "TTImp"
    reify defs val = cantReify val "TTImp"

  export
  Reify IFieldUpdate where
    reify defs val@(NDCon _ n _ _ args)
        = case (!(full (gamma defs) n), args) of
               (NS _ (UN "ISetField"), [(_, x), (_, y)])
                    => do x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          pure (ISetField x' y')
               (NS _ (UN "ISetFieldApp"), [(_, x), (_, y)])
                    => do x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          pure (ISetFieldApp x' y')
               _ => cantReify val "IFieldUpdate"
    reify defs val = cantReify val "IFieldUpdate"

  export
  Reify AltType where
    reify defs val@(NDCon _ n _ _ args)
        = case (!(full (gamma defs) n), args) of
               (NS _ (UN "FirstSuccess"), _)
                    => pure FirstSuccess
               (NS _ (UN "Unique"), _)
                    => pure Unique
               (NS _ (UN "UniqueDefault"), [(_, x)])
                    => do x' <- reify defs !(evalClosure defs x)
                          pure (UniqueDefault x')
               _ => cantReify val "AltType"
    reify defs val = cantReify val "AltType"

  export
  Reify FnOpt where
    reify defs val@(NDCon _ n _ _ args)
        = case (!(full (gamma defs) n), args) of
               (NS _ (UN "Inline"), _) => pure Inline
               (NS _ (UN "TCInline"), _) => pure TCInline
               (NS _ (UN "Hint"), [(_, x)])
                    => do x' <- reify defs !(evalClosure defs x)
                          pure (Hint x')
               (NS _ (UN "GlobalHint"), [(_, x)])
                    => do x' <- reify defs !(evalClosure defs x)
                          pure (GlobalHint x')
               (NS _ (UN "ExternFn"), _) => pure ExternFn
               (NS _ (UN "ForeignFn"), [(_, x)])
                    => do x' <- reify defs !(evalClosure defs x)
                          pure (ForeignFn x')
               (NS _ (UN "Invertible"), _) => pure Invertible
               (NS _ (UN "Totality"), [(_, x)])
                    => do x' <- reify defs !(evalClosure defs x)
                          pure (Totality x')
               (NS _ (UN "Macro"), _) => pure Macro
               (NS _ (UN "SpecArgs"), [(_, x)])
                    => do x' <- reify defs !(evalClosure defs x)
                          pure (SpecArgs x')
               _ => cantReify val "FnOpt"
    reify defs val = cantReify val "FnOpt"

  export
  Reify ImpTy where
    reify defs val@(NDCon _ n _ _ args)
        = case (!(full (gamma defs) n), map snd args) of
               (NS _ (UN "MkTy"), [w, x, y, z])
                    => do w' <- reify defs !(evalClosure defs w)
                          x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          z' <- reify defs !(evalClosure defs z)
                          pure (MkImpTy w' x' y' z')
               _ => cantReify val "ITy"
    reify defs val = cantReify val "ITy"

  export
  Reify DataOpt where
    reify defs val@(NDCon _ n _ _ args)
        = case (!(full (gamma defs) n), args) of
               (NS _ (UN "SearchBy"), [(_, x)])
                    => do x' <- reify defs !(evalClosure defs x)
                          pure (SearchBy x')
               (NS _ (UN "NoHints"), _) => pure NoHints
               (NS _ (UN "UniqueSearch"), _) => pure UniqueSearch
               (NS _ (UN "External"), _) => pure External
               (NS _ (UN "NoNewtype"), _) => pure NoNewtype
               _ => cantReify val "DataOpt"
    reify defs val = cantReify val "DataOpt"

  export
  Reify ImpData where
    reify defs val@(NDCon _ n _ _ args)
        = case (!(full (gamma defs) n), map snd args) of
               (NS _ (UN "MkData"), [v,w,x,y,z])
                    => do v' <- reify defs !(evalClosure defs v)
                          w' <- reify defs !(evalClosure defs w)
                          x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          z' <- reify defs !(evalClosure defs z)
                          pure (MkImpData v' w' x' y' z')
               (NS _ (UN "MkLater"), [x,y,z])
                    => do x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          z' <- reify defs !(evalClosure defs z)
                          pure (MkImpLater x' y' z')
               _ => cantReify val "Data"
    reify defs val = cantReify val "Data"

  export
  Reify IField where
    reify defs val@(NDCon _ n _ _ args)
        = case (!(full (gamma defs) n), map snd args) of
               (NS _ (UN "MkIField"), [v,w,x,y,z])
                    => do v' <- reify defs !(evalClosure defs v)
                          w' <- reify defs !(evalClosure defs w)
                          x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          z' <- reify defs !(evalClosure defs z)
                          pure (MkIField v' w' x' y' z')
               _ => cantReify val "IField"
    reify defs val = cantReify val "IField"

  export
  Reify ImpRecord where
    reify defs val@(NDCon _ n _ _ args)
        = case (!(full (gamma defs) n), map snd args) of
               (NS _ (UN "MkRecord"), [v,w,x,y,z])
                    => do v' <- reify defs !(evalClosure defs v)
                          w' <- reify defs !(evalClosure defs w)
                          x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          z' <- reify defs !(evalClosure defs z)
                          pure (MkImpRecord v' w' x' y' z')
               _ => cantReify val "Record"
    reify defs val = cantReify val "Record"

  export
  Reify ImpClause where
    reify defs val@(NDCon _ n _ _ args)
        = case (!(full (gamma defs) n), map snd args) of
               (NS _ (UN "PatClause"), [x,y,z])
                    => do x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          z' <- reify defs !(evalClosure defs z)
                          pure (PatClause x' y' z')
               (NS _ (UN "WithClause"), [v,w,x,y,z])
                    => do v' <- reify defs !(evalClosure defs v)
                          w' <- reify defs !(evalClosure defs w)
                          x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          z' <- reify defs !(evalClosure defs z)
                          pure (WithClause v' w' x' y' [] z')
               (NS _ (UN "ImpossibleClause"), [x,y])
                    => do x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          pure (ImpossibleClause x' y')
               _ => cantReify val "Clause"
    reify defs val = cantReify val "Clause"

  export
  Reify ImpDecl where
    reify defs val@(NDCon _ n _ _ args)
        = case (!(full (gamma defs) n), map snd args) of
               (NS _ (UN "IClaim"), [v,w,x,y,z])
                    => do v' <- reify defs !(evalClosure defs v)
                          w' <- reify defs !(evalClosure defs w)
                          x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          z' <- reify defs !(evalClosure defs z)
                          pure (IClaim v' w' x' y' z')
               (NS _ (UN "IData"), [x,y,z])
                    => do x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          z' <- reify defs !(evalClosure defs z)
                          pure (IData x' y' z')
               (NS _ (UN "IDef"), [x,y,z])
                    => do x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          z' <- reify defs !(evalClosure defs z)
                          pure (IDef x' y' z')
               (NS _ (UN "IParameters"), [x,y,z])
                    => do x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          z' <- reify defs !(evalClosure defs z)
                          pure (IParameters x' y' z')
               (NS _ (UN "IRecord"), [x,y,z])
                    => do x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          z' <- reify defs !(evalClosure defs z)
                          pure (IRecord x' Nothing y' z')
               (NS _ (UN "INamespace"), [w,x,y])
                    => do w' <- reify defs !(evalClosure defs w)
                          x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          pure (INamespace w' x' y')
               (NS _ (UN "ITransform"), [w,x,y,z])
                    => do w' <- reify defs !(evalClosure defs w)
                          x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          z' <- reify defs !(evalClosure defs z)
                          pure (ITransform w' x' y' z')
               (NS _ (UN "ILog"), [x])
                    => do x' <- reify defs !(evalClosure defs x)
                          pure (ILog x')
               _ => cantReify val "Decl"
    reify defs val = cantReify val "Decl"

mutual
  export
  Reflect RawImp where
    reflect fc defs lhs env (IVar tfc n)
        = do fc' <- reflect fc defs lhs env tfc
             n' <- reflect fc defs lhs env n
             appCon fc defs (reflectionttimp "IVar") [fc', n']
    reflect fc defs lhs env (IPi tfc c p mn aty rty)
        = do fc' <- reflect fc defs lhs env tfc
             c' <- reflect fc defs lhs env c
             p' <- reflect fc defs lhs env p
             mn' <- reflect fc defs lhs env mn
             aty' <- reflect fc defs lhs env aty
             rty' <- reflect fc defs lhs env rty
             appCon fc defs (reflectionttimp "IPi") [fc', c', p', mn', aty', rty']
    reflect fc defs lhs env (ILam tfc c p mn aty rty)
        = do fc' <- reflect fc defs lhs env tfc
             c' <- reflect fc defs lhs env c
             p' <- reflect fc defs lhs env p
             mn' <- reflect fc defs lhs env mn
             aty' <- reflect fc defs lhs env aty
             rty' <- reflect fc defs lhs env rty
             appCon fc defs (reflectionttimp "ILam") [fc', c', p', mn', aty', rty']
    reflect fc defs lhs env (ILet tfc lhsFC c n aty aval sc)
        = do fc' <- reflect fc defs lhs env tfc
             lhsFC' <- reflect fc defs lhs env lhsFC
             c' <- reflect fc defs lhs env c
             n' <- reflect fc defs lhs env n
             aty' <- reflect fc defs lhs env aty
             aval' <- reflect fc defs lhs env aval
             sc' <- reflect fc defs lhs env sc
             appCon fc defs (reflectionttimp "ILet") [fc', lhsFC', c', n', aty', aval', sc']
    reflect fc defs lhs env (ICase tfc sc ty cs)
        = do fc' <- reflect fc defs lhs env tfc
             sc' <- reflect fc defs lhs env sc
             ty' <- reflect fc defs lhs env ty
             cs' <- reflect fc defs lhs env cs
             appCon fc defs (reflectionttimp "ICase") [fc', sc', ty', cs']
    reflect fc defs lhs env (ILocal tfc ds sc)
        = do fc' <- reflect fc defs lhs env tfc
             ds' <- reflect fc defs lhs env ds
             sc' <- reflect fc defs lhs env sc
             appCon fc defs (reflectionttimp "ILocal") [fc', ds', sc']
    reflect fc defs lhs env (ICaseLocal tfc u i args t)
        = reflect fc defs lhs env t -- shouldn't see this anyway...
    reflect fc defs lhs env (IUpdate tfc ds sc)
        = do fc' <- reflect fc defs lhs env tfc
             ds' <- reflect fc defs lhs env ds
             sc' <- reflect fc defs lhs env sc
             appCon fc defs (reflectionttimp "IUpdate") [fc', ds', sc']
    reflect fc defs lhs env (IApp tfc f a)
        = do fc' <- reflect fc defs lhs env tfc
             f' <- reflect fc defs lhs env f
             a' <- reflect fc defs lhs env a
             appCon fc defs (reflectionttimp "IApp") [fc', f', a']
    reflect fc defs lhs env (IAutoApp tfc f a)
        = do fc' <- reflect fc defs lhs env tfc
             f' <- reflect fc defs lhs env f
             a' <- reflect fc defs lhs env a
             appCon fc defs (reflectionttimp "IAutoApp") [fc', f', a']
    reflect fc defs lhs env (INamedApp tfc f m a)
        = do fc' <- reflect fc defs lhs env tfc
             f' <- reflect fc defs lhs env f
             m' <- reflect fc defs lhs env m
             a' <- reflect fc defs lhs env a
             appCon fc defs (reflectionttimp "INamedApp") [fc', f', m', a']
    reflect fc defs lhs env (IWithApp tfc f a)
        = do fc' <- reflect fc defs lhs env tfc
             f' <- reflect fc defs lhs env f
             a' <- reflect fc defs lhs env a
             appCon fc defs (reflectionttimp "IWithApp") [fc', f', a']
    reflect fc defs lhs env (ISearch tfc d)
        = do fc' <- reflect fc defs lhs env tfc
             d' <- reflect fc defs lhs env d
             appCon fc defs (reflectionttimp "ISearch") [fc', d']
    reflect fc defs lhs env (IAlternative tfc t as)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             as' <- reflect fc defs lhs env as
             appCon fc defs (reflectionttimp "IAlternative") [fc', t', as']
    reflect fc defs lhs env (IRewrite tfc t sc)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             sc' <- reflect fc defs lhs env sc
             appCon fc defs (reflectionttimp "IRewrite") [fc', t', sc']
    reflect fc defs lhs env (ICoerced tfc d) = reflect fc defs lhs env d
    reflect fc defs lhs env (IBindHere tfc n sc)
        = do fc' <- reflect fc defs lhs env tfc
             n' <- reflect fc defs lhs env n
             sc' <- reflect fc defs lhs env sc
             appCon fc defs (reflectionttimp "IBindHere") [fc', n', sc']
    reflect fc defs lhs env (IBindVar tfc n)
        = do fc' <- reflect fc defs lhs env tfc
             n' <- reflect fc defs lhs env n
             appCon fc defs (reflectionttimp "IBindVar") [fc', n']
    reflect fc defs lhs env (IAs tfc nameFC s n t)
        = do fc' <- reflect fc defs lhs env tfc
             nameFC' <- reflect fc defs lhs env nameFC
             s' <- reflect fc defs lhs env s
             n' <- reflect fc defs lhs env n
             t' <- reflect fc defs lhs env t
             appCon fc defs (reflectionttimp "IAs") [fc', nameFC', s', n', t']
    reflect fc defs lhs env (IMustUnify tfc r t)
        = do fc' <- reflect fc defs lhs env tfc
             r' <- reflect fc defs lhs env r
             t' <- reflect fc defs lhs env t
             appCon fc defs (reflectionttimp "IMustUnify") [fc', r', t']
    reflect fc defs lhs env (IDelayed tfc r t)
        = do fc' <- reflect fc defs lhs env tfc
             r' <- reflect fc defs lhs env r
             t' <- reflect fc defs lhs env t
             appCon fc defs (reflectionttimp "IDelayed") [fc', r', t']
    reflect fc defs lhs env (IDelay tfc t)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             appCon fc defs (reflectionttimp "IDelay") [fc', t']
    reflect fc defs lhs env (IForce tfc t)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             appCon fc defs (reflectionttimp "IForce") [fc', t']
    reflect fc defs lhs env (IQuote tfc t)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             appCon fc defs (reflectionttimp "IQuote") [fc', t']
    reflect fc defs lhs env (IQuoteName tfc t)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             appCon fc defs (reflectionttimp "IQuoteName") [fc', t']
    reflect fc defs lhs env (IQuoteDecl tfc t)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             appCon fc defs (reflectionttimp "IQuoteDecl") [fc', t']
    reflect fc defs lhs env (IUnquote tfc (IVar _ t))
        = pure (Ref tfc Bound t)
    reflect fc defs lhs env (IUnquote tfc t)
        = throw (InternalError "Can't reflect an unquote: escapes should be lifted out")
    reflect fc defs lhs env (IRunElab tfc t)
        = throw (InternalError "Can't reflect a %runelab")
    reflect fc defs lhs env (IPrimVal tfc t)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             appCon fc defs (reflectionttimp "IPrimVal") [fc', t']
    reflect fc defs lhs env (IType tfc)
        = do fc' <- reflect fc defs lhs env tfc
             appCon fc defs (reflectionttimp "IType") [fc']
    reflect fc defs lhs env (IHole tfc t)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             appCon fc defs (reflectionttimp "IHole") [fc', t']
    reflect fc defs lhs env (IUnifyLog tfc _ t)
        = reflect fc defs lhs env t
    reflect fc defs True env (Implicit tfc t)
        = pure (Erased fc False)
    reflect fc defs lhs env (Implicit tfc t)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             appCon fc defs (reflectionttimp "Implicit") [fc', t']
    reflect fc defs lhs env (IWithUnambigNames tfc ns t)
        = do fc' <- reflect fc defs lhs env tfc
             ns' <- reflect fc defs lhs env ns
             t' <- reflect fc defs lhs env t
             appCon fc defs (reflectionttimp "WithUnambigNames") [fc', ns', t']

  export
  Reflect IFieldUpdate where
    reflect fc defs lhs env (ISetField p t)
        = do p' <- reflect fc defs lhs env p
             t' <- reflect fc defs lhs env t
             appCon fc defs (reflectionttimp "ISetField") [p', t']
    reflect fc defs lhs env (ISetFieldApp p t)
        = do p' <- reflect fc defs lhs env p
             t' <- reflect fc defs lhs env t
             appCon fc defs (reflectionttimp "ISetFieldApp") [p', t']

  export
  Reflect AltType where
    reflect fc defs lhs env FirstSuccess = getCon fc defs (reflectionttimp "FirstSuccess")
    reflect fc defs lhs env Unique = getCon fc defs (reflectionttimp "Unique")
    reflect fc defs lhs env (UniqueDefault x)
        = do x' <- reflect fc defs lhs env x
             appCon fc defs (reflectionttimp "UniqueDefault") [x']

  export
  Reflect FnOpt where
    reflect fc defs lhs env Inline = getCon fc defs (reflectionttimp "Inline")
    reflect fc defs lhs env TCInline = getCon fc defs (reflectionttimp "TCInline")
    reflect fc defs lhs env (Hint x)
        = do x' <- reflect fc defs lhs env x
             appCon fc defs (reflectionttimp "Hint") [x']
    reflect fc defs lhs env (GlobalHint x)
        = do x' <- reflect fc defs lhs env x
             appCon fc defs (reflectionttimp "GlobalHint") [x']
    reflect fc defs lhs env ExternFn = getCon fc defs (reflectionttimp "ExternFn")
    reflect fc defs lhs env (ForeignFn x)
        = do x' <- reflect fc defs lhs env x
             appCon fc defs (reflectionttimp "ForeignFn") [x']
    reflect fc defs lhs env Invertible = getCon fc defs (reflectionttimp "Invertible")
    reflect fc defs lhs env (Totality r)
        = do r' <- reflect fc defs lhs env r
             appCon fc defs (reflectionttimp "Totality") [r']
    reflect fc defs lhs env Macro = getCon fc defs (reflectionttimp "Macro")
    reflect fc defs lhs env (SpecArgs r)
        = do r' <- reflect fc defs lhs env r
             appCon fc defs (reflectionttimp "SpecArgs") [r']

  export
  Reflect ImpTy where
    reflect fc defs lhs env (MkImpTy w x y z)
        = do w' <- reflect fc defs lhs env w
             x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appCon fc defs (reflectionttimp "MkTy") [w', x', y', z']

  export
  Reflect DataOpt where
    reflect fc defs lhs env (SearchBy x)
        = do x' <- reflect fc defs lhs env x
             appCon fc defs (reflectionttimp "SearchBy") [x']
    reflect fc defs lhs env NoHints = getCon fc defs (reflectionttimp "NoHints")
    reflect fc defs lhs env UniqueSearch = getCon fc defs (reflectionttimp "UniqueSearch")
    reflect fc defs lhs env External = getCon fc defs (reflectionttimp "External")
    reflect fc defs lhs env NoNewtype = getCon fc defs (reflectionttimp "NoNewtype")

  export
  Reflect ImpData where
    reflect fc defs lhs env (MkImpData v w x y z)
        = do v' <- reflect fc defs lhs env v
             w' <- reflect fc defs lhs env w
             x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appCon fc defs (reflectionttimp "MkData") [v', w', x', y', z']
    reflect fc defs lhs env (MkImpLater x y z)
        = do x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appCon fc defs (reflectionttimp "MkLater") [x', y', z']

  export
  Reflect IField where
    reflect fc defs lhs env (MkIField v w x y z)
        = do v' <- reflect fc defs lhs env v
             w' <- reflect fc defs lhs env w
             x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appCon fc defs (reflectionttimp "MkIField") [v', w', x', y', z']

  export
  Reflect ImpRecord where
    reflect fc defs lhs env (MkImpRecord v w x y z)
        = do v' <- reflect fc defs lhs env v
             w' <- reflect fc defs lhs env w
             x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appCon fc defs (reflectionttimp "MkRecord") [v', w', x', y', z']

  export
  Reflect ImpClause where
    reflect fc defs lhs env (PatClause x y z)
        = do x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appCon fc defs (reflectionttimp "PatClause") [x', y', z']
    reflect fc defs lhs env (WithClause u v w x y z)
        = do u' <- reflect fc defs lhs env u
             v' <- reflect fc defs lhs env v
             w' <- reflect fc defs lhs env w
             x' <- reflect fc defs lhs env x
             z' <- reflect fc defs lhs env z
             appCon fc defs (reflectionttimp "WithClause") [u', v', w', x', z']
    reflect fc defs lhs env (ImpossibleClause x y)
        = do x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             appCon fc defs (reflectionttimp "ImpossibleClause") [x', y']

  export
  Reflect ImpDecl where
    reflect fc defs lhs env (IClaim v w x y z)
        = do v' <- reflect fc defs lhs env v
             w' <- reflect fc defs lhs env w
             x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appCon fc defs (reflectionttimp "IClaim") [v', w', x', y', z']
    reflect fc defs lhs env (IData x y z)
        = do x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appCon fc defs (reflectionttimp "IData") [x', y', z']
    reflect fc defs lhs env (IDef x y z)
        = do x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appCon fc defs (reflectionttimp "IDef") [x', y', z']
    reflect fc defs lhs env (IParameters x y z)
        = do x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appCon fc defs (reflectionttimp "IParameters") [x', y', z']
    reflect fc defs lhs env (IRecord x _ y z)
        = do x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appCon fc defs (reflectionttimp "IRecord") [x', y', z']
    reflect fc defs lhs env (INamespace x y z)
        = do x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appCon fc defs (reflectionttimp "INamespace") [x', y', z']
    reflect fc defs lhs env (ITransform w x y z)
        = do w' <- reflect fc defs lhs env w
             x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appCon fc defs (reflectionttimp "ITransform") [w', x', y', z']
    reflect fc defs lhs env (IRunElabDecl w x)
        = throw (GenericMsg fc "Can't reflect a %runElab")
    reflect fc defs lhs env (IPragma _ x)
        = throw (GenericMsg fc "Can't reflect a pragma")
    reflect fc defs lhs env (ILog x)
        = do x' <- reflect fc defs lhs env x
             appCon fc defs (reflectionttimp "ILog") [x']
