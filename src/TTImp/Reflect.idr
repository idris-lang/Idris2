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
  reify defs (NDCon _ (NS _ (UN "PI")) _ _ [c])
      = do c' <- reify defs !(evalClosure defs c)
           pure (PI c')
  reify defs (NDCon _ (NS _ (UN "PATTERN")) _ _ _)
      = pure PATTERN
  reify defs (NDCon _ (NS _ (UN "NONE")) _ _ _)
      = pure NONE
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
  reify defs (NDCon _ (NS _ (UN "UseLeft")) _ _ _)
      = pure UseLeft
  reify defs (NDCon _ (NS _ (UN "UseRight")) _ _ _)
      = pure UseRight
  reify defs val = cantReify val "UseSide"

export
Reflect UseSide where
  reflect fc defs env UseLeft
      = getCon fc defs (reflectionttimp "UseLeft")
  reflect fc defs env UseRight
      = getCon fc defs (reflectionttimp "UseRight")

export
Reify DotReason where
  reify defs (NDCon _ (NS _ (UN "NonLinearVar")) _ _ _)
      = pure NonLinearVar
  reify defs (NDCon _ (NS _ (UN "VarApplied")) _ _ _)
      = pure VarApplied
  reify defs (NDCon _ (NS _ (UN "NotConstructor")) _ _ _)
      = pure NotConstructor
  reify defs (NDCon _ (NS _ (UN "ErasedArg")) _ _ _)
      = pure ErasedArg
  reify defs (NDCon _ (NS _ (UN "UserDotted")) _ _ _)
      = pure UserDotted
  reify defs (NDCon _ (NS _ (UN "UnknownDot")) _ _ _)
      = pure UnknownDot
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
    reify defs (NDCon _ (NS _ (UN "IVar")) _ _ [fc, n])
        = do fc' <- reify defs !(evalClosure defs fc)
             n' <- reify defs !(evalClosure defs n)
             pure (IVar fc' n')
    reify defs (NDCon _ (NS _ (UN "IPi")) _ _ [fc, c, p, mn, aty, rty])
        = do fc' <- reify defs !(evalClosure defs fc)
             c' <- reify defs !(evalClosure defs c)
             p' <- reify defs !(evalClosure defs p)
             mn' <- reify defs !(evalClosure defs mn)
             aty' <- reify defs !(evalClosure defs aty)
             rty' <- reify defs !(evalClosure defs rty)
             pure (IPi fc' c' p' mn' aty' rty')
    reify defs (NDCon _ (NS _ (UN "ILam")) _ _ [fc, c, p, mn, aty, lty])
        = do fc' <- reify defs !(evalClosure defs fc)
             c' <- reify defs !(evalClosure defs c)
             p' <- reify defs !(evalClosure defs p)
             mn' <- reify defs !(evalClosure defs mn)
             aty' <- reify defs !(evalClosure defs aty)
             lty' <- reify defs !(evalClosure defs lty)
             pure (ILam fc' c' p' mn' aty' lty')
    reify defs (NDCon _ (NS _ (UN "ILet")) _ _ [fc, c, n, ty, val, sc])
        = do fc' <- reify defs !(evalClosure defs fc)
             c' <- reify defs !(evalClosure defs c)
             n' <- reify defs !(evalClosure defs n)
             ty' <- reify defs !(evalClosure defs ty)
             val' <- reify defs !(evalClosure defs val)
             sc' <- reify defs !(evalClosure defs sc)
             pure (ILet fc' c' n' ty' val' sc')
    reify defs (NDCon _ (NS _ (UN "ICase")) _ _ [fc, sc, ty, cs])
        = do fc' <- reify defs !(evalClosure defs fc)
             sc' <- reify defs !(evalClosure defs sc)
             ty' <- reify defs !(evalClosure defs ty)
             cs' <- reify defs !(evalClosure defs cs)
             pure (ICase fc' sc' ty' cs')
    reify defs (NDCon _ (NS _ (UN "ILocal")) _ _ [fc, ds, sc])
        = do fc' <- reify defs !(evalClosure defs fc)
             ds' <- reify defs !(evalClosure defs ds)
             sc' <- reify defs !(evalClosure defs sc)
             pure (ILocal fc' ds' sc')
    reify defs (NDCon _ (NS _ (UN "IUpdate")) _ _ [fc, ds, sc])
        = do fc' <- reify defs !(evalClosure defs fc)
             ds' <- reify defs !(evalClosure defs ds)
             sc' <- reify defs !(evalClosure defs sc)
             pure (IUpdate fc' ds' sc')
    reify defs (NDCon _ (NS _ (UN "IApp")) _ _ [fc, f, a])
        = do fc' <- reify defs !(evalClosure defs fc)
             f' <- reify defs !(evalClosure defs f)
             a' <- reify defs !(evalClosure defs a)
             pure (IApp fc' f' a')
    reify defs (NDCon _ (NS _ (UN "IImplicitApp")) _ _ [fc, f, m, a])
        = do fc' <- reify defs !(evalClosure defs fc)
             f' <- reify defs !(evalClosure defs f)
             m' <- reify defs !(evalClosure defs m)
             a' <- reify defs !(evalClosure defs a)
             pure (IImplicitApp fc' f' m' a')
    reify defs (NDCon _ (NS _ (UN "IWithApp")) _ _ [fc, f, a])
        = do fc' <- reify defs !(evalClosure defs fc)
             f' <- reify defs !(evalClosure defs f)
             a' <- reify defs !(evalClosure defs a)
             pure (IWithApp fc' f' a')
    reify defs (NDCon _ (NS _ (UN "ISearch")) _ _ [fc, d])
        = do fc' <- reify defs !(evalClosure defs fc)
             d' <- reify defs !(evalClosure defs d)
             pure (ISearch fc' d')
    reify defs (NDCon _ (NS _ (UN "IAlternative")) _ _ [fc, t, as])
        = do fc' <- reify defs !(evalClosure defs fc)
             t' <- reify defs !(evalClosure defs t)
             as' <- reify defs !(evalClosure defs as)
             pure (IAlternative fc' t' as')
    reify defs (NDCon _ (NS _ (UN "IRewrite")) _ _ [fc, t, sc])
        = do fc' <- reify defs !(evalClosure defs fc)
             t' <- reify defs !(evalClosure defs t)
             sc' <- reify defs !(evalClosure defs sc)
             pure (IRewrite fc' t' sc')
    reify defs (NDCon _ (NS _ (UN "IBindHere")) _ _ [fc, t, sc])
        = do fc' <- reify defs !(evalClosure defs fc)
             t' <- reify defs !(evalClosure defs t)
             sc' <- reify defs !(evalClosure defs sc)
             pure (IBindHere fc' t' sc')
    reify defs (NDCon _ (NS _ (UN "IBindVar")) _ _ [fc, n])
        = do fc' <- reify defs !(evalClosure defs fc)
             n' <- reify defs !(evalClosure defs n)
             pure (IBindVar fc' n')
    reify defs (NDCon _ (NS _ (UN "IAs")) _ _ [fc, s, n, t])
        = do fc' <- reify defs !(evalClosure defs fc)
             s' <- reify defs !(evalClosure defs s)
             n' <- reify defs !(evalClosure defs n)
             t' <- reify defs !(evalClosure defs t)
             pure (IAs fc' s' n' t')
    reify defs (NDCon _ (NS _ (UN "IMustUnify")) _ _ [fc, r, t])
        = do fc' <- reify defs !(evalClosure defs fc)
             r' <- reify defs !(evalClosure defs r)
             t' <- reify defs !(evalClosure defs t)
             pure (IMustUnify fc' r' t')
    reify defs (NDCon _ (NS _ (UN "IDelayed")) _ _ [fc, r, t])
        = do fc' <- reify defs !(evalClosure defs fc)
             r' <- reify defs !(evalClosure defs r)
             t' <- reify defs !(evalClosure defs t)
             pure (IDelayed fc' r' t')
    reify defs (NDCon _ (NS _ (UN "IDelay")) _ _ [fc, t])
        = do fc' <- reify defs !(evalClosure defs fc)
             t' <- reify defs !(evalClosure defs t)
             pure (IDelay fc' t')
    reify defs (NDCon _ (NS _ (UN "IForce")) _ _ [fc, t])
        = do fc' <- reify defs !(evalClosure defs fc)
             t' <- reify defs !(evalClosure defs t)
             pure (IForce fc' t')
    reify defs (NDCon _ (NS _ (UN "IQuote")) _ _ [fc, t])
        = do fc' <- reify defs !(evalClosure defs fc)
             t' <- reify defs !(evalClosure defs t)
             pure (IQuote fc' t')
    reify defs (NDCon _ (NS _ (UN "IQuoteDecl")) _ _ [fc, t])
        = do fc' <- reify defs !(evalClosure defs fc)
             t' <- reify defs !(evalClosure defs t)
             pure (IQuoteDecl fc' t')
    reify defs (NDCon _ (NS _ (UN "IUnquote")) _ _ [fc, t])
        = do fc' <- reify defs !(evalClosure defs fc)
             t' <- reify defs !(evalClosure defs t)
             pure (IUnquote fc' t')
    reify defs (NDCon _ (NS _ (UN "IPrimVal")) _ _ [fc, t])
        = do fc' <- reify defs !(evalClosure defs fc)
             t' <- reify defs !(evalClosure defs t)
             pure (IPrimVal fc' t')
    reify defs (NDCon _ (NS _ (UN "IType")) _ _ [fc])
        = do fc' <- reify defs !(evalClosure defs fc)
             pure (IType fc')
    reify defs (NDCon _ (NS _ (UN "IHole")) _ _ [fc, n])
        = do fc' <- reify defs !(evalClosure defs fc)
             n' <- reify defs !(evalClosure defs n)
             pure (IHole fc' n')
    reify defs (NDCon _ (NS _ (UN "Implicit")) _ _ [fc, n])
        = do fc' <- reify defs !(evalClosure defs fc)
             n' <- reify defs !(evalClosure defs n)
             pure (Implicit fc' n')
    reify defs (NDCon _ (NS _ (UN "IWithUnambigNames")) _ _ [fc, ns, t])
        = do fc' <- reify defs !(evalClosure defs fc)
             ns' <- reify defs !(evalClosure defs ns)
             t' <- reify defs !(evalClosure defs t)
             pure (IWithUnambigNames fc' ns' t')
    reify defs val = cantReify val "TTImp"

  export
  Reify IFieldUpdate where
    reify defs (NDCon _ (NS _ (UN "ISetField")) _ _ [x, y])
        = do x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             pure (ISetField x' y')
    reify defs (NDCon _ (NS _ (UN "ISetFieldApp")) _ _ [x, y])
        = do x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             pure (ISetFieldApp x' y')
    reify defs val = cantReify val "IFieldUpdate"

  export
  Reify AltType where
    reify defs (NDCon _ (NS _ (UN "FirstSuccess")) _ _ _)
        = pure FirstSuccess
    reify defs (NDCon _ (NS _ (UN "Unique")) _ _ _)
        = pure Unique
    reify defs (NDCon _ (NS _ (UN "UniqueDefault")) _ _ [x])
        = do x' <- reify defs !(evalClosure defs x)
             pure (UniqueDefault x')
    reify defs val = cantReify val "AltType"

  export
  Reify FnOpt where
    reify defs (NDCon _ (NS _ (UN "Inline")) _ _ _)
        = pure Inline
    reify defs (NDCon _ (NS _ (UN "TCInline")) _ _ _)
        = pure TCInline
    reify defs (NDCon _ (NS _ (UN "Hint")) _ _ [x])
        = do x' <- reify defs !(evalClosure defs x)
             pure (Hint x')
    reify defs (NDCon _ (NS _ (UN "GlobalHint")) _ _ [x])
        = do x' <- reify defs !(evalClosure defs x)
             pure (GlobalHint x')
    reify defs (NDCon _ (NS _ (UN "ExternFn")) _ _ _)
        = pure ExternFn
    reify defs (NDCon _ (NS _ (UN "ForeignFn")) _ _ [x])
        = do x' <- reify defs !(evalClosure defs x)
             pure (ForeignFn x')
    reify defs (NDCon _ (NS _ (UN "Invertible")) _ _ _)
        = pure Invertible
    reify defs (NDCon _ (NS _ (UN "Totality")) _ _ [x])
        = do x' <- reify defs !(evalClosure defs x)
             pure (Totality x')
    reify defs (NDCon _ (NS _ (UN "Macro")) _ _ _)
        = pure Macro
    reify defs (NDCon _ (NS _ (UN "SpecArgs")) _ _ [x])
        = do x' <- reify defs !(evalClosure defs x)
             pure (SpecArgs x')
    reify defs val = cantReify val "FnOpt"

  export
  Reify ImpTy where
    reify defs (NDCon _ (NS _ (UN "MkTy")) _ _ [x,y,z])
        = do x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             z' <- reify defs !(evalClosure defs z)
             pure (MkImpTy x' y' z')
    reify defs val = cantReify val "ITy"

  export
  Reify DataOpt where
    reify defs (NDCon _ (NS _ (UN "SearchBy")) _ _ [x])
        = do x' <- reify defs !(evalClosure defs x)
             pure (SearchBy x')
    reify defs (NDCon _ (NS _ (UN "NoHints")) _ _ _)
        = pure NoHints
    reify defs (NDCon _ (NS _ (UN "UniqueSearch")) _ _ _)
        = pure UniqueSearch
    reify defs (NDCon _ (NS _ (UN "External")) _ _ _)
        = pure External
    reify defs (NDCon _ (NS _ (UN "NoNewtype")) _ _ _)
        = pure NoNewtype
    reify defs val = cantReify val "DataOpt"

  export
  Reify ImpData where
    reify defs (NDCon _ (NS _ (UN "MkData")) _ _ [v,w,x,y,z])
        = do v' <- reify defs !(evalClosure defs v)
             w' <- reify defs !(evalClosure defs w)
             x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             z' <- reify defs !(evalClosure defs z)
             pure (MkImpData v' w' x' y' z')
    reify defs (NDCon _ (NS _ (UN "MkLater")) _ _ [x,y,z])
        = do x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             z' <- reify defs !(evalClosure defs z)
             pure (MkImpLater x' y' z')
    reify defs val = cantReify val "Data"

  export
  Reify IField where
    reify defs (NDCon _ (NS _ (UN "MkIField")) _ _ [v,w,x,y,z])
        = do v' <- reify defs !(evalClosure defs v)
             w' <- reify defs !(evalClosure defs w)
             x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             z' <- reify defs !(evalClosure defs z)
             pure (MkIField v' w' x' y' z')
    reify defs val = cantReify val "IField"

  export
  Reify ImpRecord where
    reify defs (NDCon _ (NS _ (UN "MkRecord")) _ _ [v,w,x,y,z])
        = do v' <- reify defs !(evalClosure defs v)
             w' <- reify defs !(evalClosure defs w)
             x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             z' <- reify defs !(evalClosure defs z)
             pure (MkImpRecord v' w' x' y' z')
    reify defs val = cantReify val "Record"

  export
  Reify ImpClause where
    reify defs (NDCon _ (NS _ (UN "PatClause")) _ _ [x,y,z])
        = do x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             z' <- reify defs !(evalClosure defs z)
             pure (PatClause x' y' z')
    reify defs (NDCon _ (NS _ (UN "WithClause")) _ _ [w,x,y,z])
        = do w' <- reify defs !(evalClosure defs w)
             x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             z' <- reify defs !(evalClosure defs z)
             pure (WithClause w' x' y' [] z')
    reify defs (NDCon _ (NS _ (UN "ImpossibleClause")) _ _ [x,y])
        = do x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             pure (ImpossibleClause x' y')
    reify defs val = cantReify val "Clause"

  export
  Reify ImpDecl where
    reify defs (NDCon _ (NS _ (UN "IClaim")) _ _ [v,w,x,y,z])
        = do v' <- reify defs !(evalClosure defs v)
             w' <- reify defs !(evalClosure defs w)
             x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             z' <- reify defs !(evalClosure defs z)
             pure (IClaim v' w' x' y' z')
    reify defs (NDCon _ (NS _ (UN "IData")) _ _ [x,y,z])
        = do x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             z' <- reify defs !(evalClosure defs z)
             pure (IData x' y' z')
    reify defs (NDCon _ (NS _ (UN "IDef")) _ _ [x,y,z])
        = do x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             z' <- reify defs !(evalClosure defs z)
             pure (IDef x' y' z')
    reify defs (NDCon _ (NS _ (UN "IParameters")) _ _ [x,y,z])
        = do x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             z' <- reify defs !(evalClosure defs z)
             pure (IParameters x' y' z')
    reify defs (NDCon _ (NS _ (UN "IRecord")) _ _ [x,y,z])
        = do x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             z' <- reify defs !(evalClosure defs z)
             pure (IRecord x' Nothing y' z')
    reify defs (NDCon _ (NS _ (UN "INamespace")) _ _ [w,x,y])
        = do w' <- reify defs !(evalClosure defs w)
             x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             pure (INamespace w' x' y')
    reify defs (NDCon _ (NS _ (UN "ITransform")) _ _ [w,x,y,z])
        = do w' <- reify defs !(evalClosure defs w)
             x' <- reify defs !(evalClosure defs x)
             y' <- reify defs !(evalClosure defs y)
             z' <- reify defs !(evalClosure defs z)
             pure (ITransform w' x' y' z')
    reify defs (NDCon _ (NS _ (UN "ILog")) _ _ [x])
        = do x' <- reify defs !(evalClosure defs x)
             pure (ILog x')
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
    reflect fc defs env (IPragma x)
        = throw (GenericMsg fc "Can't reflect a pragma")
    reflect fc defs env (ILog x)
        = do x' <- reflect fc defs env x
             appCon fc defs (reflectionttimp "ILog") [x']
