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
             (NS _ (UN "PI"), [c])
                 => do c' <- reify defs !(evalClosure defs c)
                       pure (PI c')
             (NS _ (UN "PATTERN"), _) => pure PATTERN
             (NS _ (UN "NONE"), _) => pure NONE
             _ => cantReify val "BindMode"
  reify deva val = cantReify val "BindMode"

export
Reflect BindMode where
  reflect fc defs env (PI c)
      = do c' <- reflect fc defs env c
           appCon fc defs (reflectionttimp "PI") [c']
  reflect fc defs env PATTERN
      = getCon fc defs (reflectionttimp "PATTERN")
  reflect fc defs env NONE
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
  reflect fc defs env UseLeft
      = getCon fc defs (reflectionttimp "UseLeft")
  reflect fc defs env UseRight
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
             _ => cantReify val "DotReason"
  reify defs val = cantReify val "DotReason"

export
Reflect DotReason where
  reflect fc defs env NonLinearVar
      = getCon fc defs (reflectionttimp "NonLinearVar")
  reflect fc defs env VarApplied
      = getCon fc defs (reflectionttimp "VarApplied")
  reflect fc defs env NotConstructor
      = getCon fc defs (reflectionttimp "NotConstructor")
  reflect fc defs env ErasedArg
      = getCon fc defs (reflectionttimp "ErasedArg")
  reflect fc defs env UserDotted
      = getCon fc defs (reflectionttimp "UserDotted")
  reflect fc defs env UnknownDot
      = getCon fc defs (reflectionttimp "UnknownDot")

mutual
  export
  Reify RawImp where
    reify defs val@(NDCon _ n _ _ args)
        = case (!(full (gamma defs) n), args) of
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
               (NS _ (UN "ILet"), [fc, c, n, ty, val, sc])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          c' <- reify defs !(evalClosure defs c)
                          n' <- reify defs !(evalClosure defs n)
                          ty' <- reify defs !(evalClosure defs ty)
                          val' <- reify defs !(evalClosure defs val)
                          sc' <- reify defs !(evalClosure defs sc)
                          pure (ILet fc' c' n' ty' val' sc')
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
               (NS _ (UN "IImplicitApp"), [fc, f, m, a])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          f' <- reify defs !(evalClosure defs f)
                          m' <- reify defs !(evalClosure defs m)
                          a' <- reify defs !(evalClosure defs a)
                          pure (IImplicitApp fc' f' m' a')
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
               (NS _ (UN "IAs"), [fc, s, n, t])
                    => do fc' <- reify defs !(evalClosure defs fc)
                          s' <- reify defs !(evalClosure defs s)
                          n' <- reify defs !(evalClosure defs n)
                          t' <- reify defs !(evalClosure defs t)
                          pure (IAs fc' s' n' t')
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
               (NS _ (UN "ISetField"), [x, y])
                    => do x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          pure (ISetField x' y')
               (NS _ (UN "ISetFieldApp"), [x, y])
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
               (NS _ (UN "UniqueDefault"), [x])
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
               (NS _ (UN "Hint"), [x])
                    => do x' <- reify defs !(evalClosure defs x)
                          pure (Hint x')
               (NS _ (UN "GlobalHint"), [x])
                    => do x' <- reify defs !(evalClosure defs x)
                          pure (GlobalHint x')
               (NS _ (UN "ExternFn"), _) => pure ExternFn
               (NS _ (UN "ForeignFn"), [x])
                    => do x' <- reify defs !(evalClosure defs x)
                          pure (ForeignFn x')
               (NS _ (UN "Invertible"), _) => pure Invertible
               (NS _ (UN "Totality"), [x])
                    => do x' <- reify defs !(evalClosure defs x)
                          pure (Totality x')
               (NS _ (UN "Macro"), _) => pure Macro
               (NS _ (UN "SpecArgs"), [x])
                    => do x' <- reify defs !(evalClosure defs x)
                          pure (SpecArgs x')
               _ => cantReify val "FnOpt"
    reify defs val = cantReify val "FnOpt"

  export
  Reify ImpTy where
    reify defs val@(NDCon _ n _ _ args)
        = case (!(full (gamma defs) n), args) of
               (NS _ (UN "MkTy"), [x,y,z])
                    => do x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          z' <- reify defs !(evalClosure defs z)
                          pure (MkImpTy x' y' z')
               _ => cantReify val "ITy"
    reify defs val = cantReify val "ITy"

  export
  Reify DataOpt where
    reify defs val@(NDCon _ n _ _ args)
        = case (!(full (gamma defs) n), args) of
               (NS _ (UN "SearchBy"), [x])
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
        = case (!(full (gamma defs) n), args) of
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
        = case (!(full (gamma defs) n), args) of
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
        = case (!(full (gamma defs) n), args) of
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
        = case (!(full (gamma defs) n), args) of
               (NS _ (UN "PatClause"), [x,y,z])
                    => do x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          z' <- reify defs !(evalClosure defs z)
                          pure (PatClause x' y' z')
               (NS _ (UN "WithClause"), [w,x,y,z])
                    => do w' <- reify defs !(evalClosure defs w)
                          x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          z' <- reify defs !(evalClosure defs z)
                          pure (WithClause w' x' y' [] z')
               (NS _ (UN "ImpossibleClause"), [x,y])
                    => do x' <- reify defs !(evalClosure defs x)
                          y' <- reify defs !(evalClosure defs y)
                          pure (ImpossibleClause x' y')
               _ => cantReify val "Clause"
    reify defs val = cantReify val "Clause"

  export
  Reify ImpDecl where
    reify defs val@(NDCon _ n _ _ args)
        = case (!(full (gamma defs) n), args) of
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
    reflect fc defs env (IVar tfc n)
        = do fc' <- reflect fc defs env tfc
             n' <- reflect fc defs env n
             appCon fc defs (reflectionttimp "IVar") [fc', n']
    reflect fc defs env (IPi tfc c p mn aty rty)
        = do fc' <- reflect fc defs env tfc
             c' <- reflect fc defs env c
             p' <- reflect fc defs env p
             mn' <- reflect fc defs env mn
             aty' <- reflect fc defs env aty
             rty' <- reflect fc defs env rty
             appCon fc defs (reflectionttimp "IPi") [fc', c', p', mn', aty', rty']
    reflect fc defs env (ILam tfc c p mn aty rty)
        = do fc' <- reflect fc defs env tfc
             c' <- reflect fc defs env c
             p' <- reflect fc defs env p
             mn' <- reflect fc defs env mn
             aty' <- reflect fc defs env aty
             rty' <- reflect fc defs env rty
             appCon fc defs (reflectionttimp "ILam") [fc', c', p', mn', aty', rty']
    reflect fc defs env (ILet tfc c n aty aval sc)
        = do fc' <- reflect fc defs env tfc
             c' <- reflect fc defs env c
             n' <- reflect fc defs env n
             aty' <- reflect fc defs env aty
             aval' <- reflect fc defs env aval
             sc' <- reflect fc defs env sc
             appCon fc defs (reflectionttimp "ILet") [fc', c', n', aty', aval', sc']
    reflect fc defs env (ICase tfc sc ty cs)
        = do fc' <- reflect fc defs env tfc
             sc' <- reflect fc defs env sc
             ty' <- reflect fc defs env ty
             cs' <- reflect fc defs env cs
             appCon fc defs (reflectionttimp "ICase") [fc', sc', ty', cs']
    reflect fc defs env (ILocal tfc ds sc)
        = do fc' <- reflect fc defs env tfc
             ds' <- reflect fc defs env ds
             sc' <- reflect fc defs env sc
             appCon fc defs (reflectionttimp "ILocal") [fc', ds', sc']
    reflect fc defs env (ICaseLocal tfc u i args t)
        = reflect fc defs env t -- shouldn't see this anyway...
    reflect fc defs env (IUpdate tfc ds sc)
        = do fc' <- reflect fc defs env tfc
             ds' <- reflect fc defs env ds
             sc' <- reflect fc defs env sc
             appCon fc defs (reflectionttimp "IUpdate") [fc', ds', sc']
    reflect fc defs env (IApp tfc f a)
        = do fc' <- reflect fc defs env tfc
             f' <- reflect fc defs env f
             a' <- reflect fc defs env a
             appCon fc defs (reflectionttimp "IApp") [fc', f', a']
    reflect fc defs env (IImplicitApp tfc f m a)
        = do fc' <- reflect fc defs env tfc
             f' <- reflect fc defs env f
             m' <- reflect fc defs env m
             a' <- reflect fc defs env a
             appCon fc defs (reflectionttimp "IImplicitApp") [fc', f', m', a']
    reflect fc defs env (IWithApp tfc f a)
        = do fc' <- reflect fc defs env tfc
             f' <- reflect fc defs env f
             a' <- reflect fc defs env a
             appCon fc defs (reflectionttimp "IWithApp") [fc', f', a']
    reflect fc defs env (ISearch tfc d)
        = do fc' <- reflect fc defs env tfc
             d' <- reflect fc defs env d
             appCon fc defs (reflectionttimp "ISearch") [fc', d']
    reflect fc defs env (IAlternative tfc t as)
        = do fc' <- reflect fc defs env tfc
             t' <- reflect fc defs env t
             as' <- reflect fc defs env as
             appCon fc defs (reflectionttimp "IAlternative") [fc', t', as']
    reflect fc defs env (IRewrite tfc t sc)
        = do fc' <- reflect fc defs env tfc
             t' <- reflect fc defs env t
             sc' <- reflect fc defs env sc
             appCon fc defs (reflectionttimp "IRewrite") [fc', t', sc']
    reflect fc defs env (ICoerced tfc d) = reflect fc defs env d
    reflect fc defs env (IBindHere tfc n sc)
        = do fc' <- reflect fc defs env tfc
             n' <- reflect fc defs env n
             sc' <- reflect fc defs env sc
             appCon fc defs (reflectionttimp "IBindHere") [fc', n', sc']
    reflect fc defs env (IBindVar tfc n)
        = do fc' <- reflect fc defs env tfc
             n' <- reflect fc defs env n
             appCon fc defs (reflectionttimp "IBindVar") [fc', n']
    reflect fc defs env (IAs tfc s n t)
        = do fc' <- reflect fc defs env tfc
             s' <- reflect fc defs env s
             n' <- reflect fc defs env n
             t' <- reflect fc defs env t
             appCon fc defs (reflectionttimp "IAs") [fc', s', n', t']
    reflect fc defs env (IMustUnify tfc r t)
        = do fc' <- reflect fc defs env tfc
             r' <- reflect fc defs env r
             t' <- reflect fc defs env t
             appCon fc defs (reflectionttimp "IMustUnify") [fc', r', t']
    reflect fc defs env (IDelayed tfc r t)
        = do fc' <- reflect fc defs env tfc
             r' <- reflect fc defs env r
             t' <- reflect fc defs env t
             appCon fc defs (reflectionttimp "IDelayed") [fc', r', t']
    reflect fc defs env (IDelay tfc t)
        = do fc' <- reflect fc defs env tfc
             t' <- reflect fc defs env t
             appCon fc defs (reflectionttimp "IDelay") [fc', t']
    reflect fc defs env (IForce tfc t)
        = do fc' <- reflect fc defs env tfc
             t' <- reflect fc defs env t
             appCon fc defs (reflectionttimp "IForce") [fc', t']
    reflect fc defs env (IQuote tfc t)
        = do fc' <- reflect fc defs env tfc
             t' <- reflect fc defs env t
             appCon fc defs (reflectionttimp "IQuote") [fc', t']
    reflect fc defs env (IQuoteName tfc t)
        = do fc' <- reflect fc defs env tfc
             t' <- reflect fc defs env t
             appCon fc defs (reflectionttimp "IQuoteName") [fc', t']
    reflect fc defs env (IQuoteDecl tfc t)
        = do fc' <- reflect fc defs env tfc
             t' <- reflect fc defs env t
             appCon fc defs (reflectionttimp "IQuoteDecl") [fc', t']
    reflect fc defs env (IUnquote tfc (IVar _ t))
        = pure (Ref tfc Bound t)
    reflect fc defs env (IUnquote tfc t)
        = throw (InternalError "Can't reflect an unquote: escapes should be lifted out")
    reflect fc defs env (IRunElab tfc t)
        = throw (InternalError "Can't reflect a %runelab")
    reflect fc defs env (IPrimVal tfc t)
        = do fc' <- reflect fc defs env tfc
             t' <- reflect fc defs env t
             appCon fc defs (reflectionttimp "IPrimVal") [fc', t']
    reflect fc defs env (IType tfc)
        = do fc' <- reflect fc defs env tfc
             appCon fc defs (reflectionttimp "IType") [fc']
    reflect fc defs env (IHole tfc t)
        = do fc' <- reflect fc defs env tfc
             t' <- reflect fc defs env t
             appCon fc defs (reflectionttimp "IHole") [fc', t']
    reflect fc defs env (IUnifyLog tfc _ t)
        = reflect fc defs env t
    reflect fc defs env (Implicit tfc t)
        = do fc' <- reflect fc defs env tfc
             t' <- reflect fc defs env t
             appCon fc defs (reflectionttimp "Implicit") [fc', t']
    reflect fc defs env (IWithUnambigNames tfc ns t)
        = do fc' <- reflect fc defs env tfc
             ns' <- reflect fc defs env ns
             t' <- reflect fc defs env t
             appCon fc defs (reflectionttimp "WithUnambigNames") [fc', ns', t']

  export
  Reflect IFieldUpdate where
    reflect fc defs env (ISetField p t)
        = do p' <- reflect fc defs env p
             t' <- reflect fc defs env t
             appCon fc defs (reflectionttimp "ISetField") [p', t']
    reflect fc defs env (ISetFieldApp p t)
        = do p' <- reflect fc defs env p
             t' <- reflect fc defs env t
             appCon fc defs (reflectionttimp "ISetFieldApp") [p', t']

  export
  Reflect AltType where
    reflect fc defs env FirstSuccess = getCon fc defs (reflectionttimp "FirstSuccess")
    reflect fc defs env Unique = getCon fc defs (reflectionttimp "Unique")
    reflect fc defs env (UniqueDefault x)
        = do x' <- reflect fc defs env x
             appCon fc defs (reflectionttimp "UniqueDefault") [x']

  export
  Reflect FnOpt where
    reflect fc defs env Inline = getCon fc defs (reflectionttimp "Inline")
    reflect fc defs env TCInline = getCon fc defs (reflectionttimp "TCInline")
    reflect fc defs env (Hint x)
        = do x' <- reflect fc defs env x
             appCon fc defs (reflectionttimp "Hint") [x']
    reflect fc defs env (GlobalHint x)
        = do x' <- reflect fc defs env x
             appCon fc defs (reflectionttimp "GlobalHint") [x']
    reflect fc defs env ExternFn = getCon fc defs (reflectionttimp "ExternFn")
    reflect fc defs env (ForeignFn x)
        = do x' <- reflect fc defs env x
             appCon fc defs (reflectionttimp "ForeignFn") [x']
    reflect fc defs env Invertible = getCon fc defs (reflectionttimp "Invertible")
    reflect fc defs env (Totality r)
        = do r' <- reflect fc defs env r
             appCon fc defs (reflectionttimp "Totality") [r']
    reflect fc defs env Macro = getCon fc defs (reflectionttimp "Macro")
    reflect fc defs env (SpecArgs r)
        = do r' <- reflect fc defs env r
             appCon fc defs (reflectionttimp "SpecArgs") [r']

  export
  Reflect ImpTy where
    reflect fc defs env (MkImpTy x y z)
        = do x' <- reflect fc defs env x
             y' <- reflect fc defs env y
             z' <- reflect fc defs env z
             appCon fc defs (reflectionttimp "MkTy") [x', y', z']

  export
  Reflect DataOpt where
    reflect fc defs env (SearchBy x)
        = do x' <- reflect fc defs env x
             appCon fc defs (reflectionttimp "SearchBy") [x']
    reflect fc defs env NoHints = getCon fc defs (reflectionttimp "NoHints")
    reflect fc defs env UniqueSearch = getCon fc defs (reflectionttimp "UniqueSearch")
    reflect fc defs env External = getCon fc defs (reflectionttimp "External")
    reflect fc defs env NoNewtype = getCon fc defs (reflectionttimp "NoNewtype")

  export
  Reflect ImpData where
    reflect fc defs env (MkImpData v w x y z)
        = do v' <- reflect fc defs env v
             w' <- reflect fc defs env w
             x' <- reflect fc defs env x
             y' <- reflect fc defs env y
             z' <- reflect fc defs env z
             appCon fc defs (reflectionttimp "MkData") [v', w', x', y', z']
    reflect fc defs env (MkImpLater x y z)
        = do x' <- reflect fc defs env x
             y' <- reflect fc defs env y
             z' <- reflect fc defs env z
             appCon fc defs (reflectionttimp "MkLater") [x', y', z']

  export
  Reflect IField where
    reflect fc defs env (MkIField v w x y z)
        = do v' <- reflect fc defs env v
             w' <- reflect fc defs env w
             x' <- reflect fc defs env x
             y' <- reflect fc defs env y
             z' <- reflect fc defs env z
             appCon fc defs (reflectionttimp "MkIField") [v', w', x', y', z']

  export
  Reflect ImpRecord where
    reflect fc defs env (MkImpRecord v w x y z)
        = do v' <- reflect fc defs env v
             w' <- reflect fc defs env w
             x' <- reflect fc defs env x
             y' <- reflect fc defs env y
             z' <- reflect fc defs env z
             appCon fc defs (reflectionttimp "MkRecord") [v', w', x', y', z']

  export
  Reflect ImpClause where
    reflect fc defs env (PatClause x y z)
        = do x' <- reflect fc defs env x
             y' <- reflect fc defs env y
             z' <- reflect fc defs env z
             appCon fc defs (reflectionttimp "PatClause") [x', y', z']
    reflect fc defs env (WithClause v w x y z)
        = do v' <- reflect fc defs env v
             w' <- reflect fc defs env w
             x' <- reflect fc defs env x
             z' <- reflect fc defs env z
             appCon fc defs (reflectionttimp "WithClause") [v', w', x', z']
    reflect fc defs env (ImpossibleClause x y)
        = do x' <- reflect fc defs env x
             y' <- reflect fc defs env y
             appCon fc defs (reflectionttimp "ImpossibleClause") [x', y']

  export
  Reflect ImpDecl where
    reflect fc defs env (IClaim v w x y z)
        = do v' <- reflect fc defs env v
             w' <- reflect fc defs env w
             x' <- reflect fc defs env x
             y' <- reflect fc defs env y
             z' <- reflect fc defs env z
             appCon fc defs (reflectionttimp "IClaim") [v', w', x', y', z']
    reflect fc defs env (IData x y z)
        = do x' <- reflect fc defs env x
             y' <- reflect fc defs env y
             z' <- reflect fc defs env z
             appCon fc defs (reflectionttimp "IData") [x', y', z']
    reflect fc defs env (IDef x y z)
        = do x' <- reflect fc defs env x
             y' <- reflect fc defs env y
             z' <- reflect fc defs env z
             appCon fc defs (reflectionttimp "IDef") [x', y', z']
    reflect fc defs env (IParameters x y z)
        = do x' <- reflect fc defs env x
             y' <- reflect fc defs env y
             z' <- reflect fc defs env z
             appCon fc defs (reflectionttimp "IParameters") [x', y', z']
    reflect fc defs env (IRecord x _ y z)
        = do x' <- reflect fc defs env x
             y' <- reflect fc defs env y
             z' <- reflect fc defs env z
             appCon fc defs (reflectionttimp "IRecord") [x', y', z']
    reflect fc defs env (INamespace x y z)
        = do x' <- reflect fc defs env x
             y' <- reflect fc defs env y
             z' <- reflect fc defs env z
             appCon fc defs (reflectionttimp "INamespace") [x', y', z']
    reflect fc defs env (ITransform w x y z)
        = do w' <- reflect fc defs env w
             x' <- reflect fc defs env x
             y' <- reflect fc defs env y
             z' <- reflect fc defs env z
             appCon fc defs (reflectionttimp "ITransform") [w', x', y', z']
    reflect fc defs env (IRunElabDecl w x)
        = throw (GenericMsg fc "Can't reflect a %runElab")
    reflect fc defs env (IPragma x)
        = throw (GenericMsg fc "Can't reflect a pragma")
    reflect fc defs env (ILog x)
        = do x' <- reflect fc defs env x
             appCon fc defs (reflectionttimp "ILog") [x']
