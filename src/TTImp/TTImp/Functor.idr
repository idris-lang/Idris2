module TTImp.TTImp.Functor

import Core.TT
import TTImp.TTImp

%default covering

mutual

  export
  Functor RawImp' where
    map f (IVar fc nm) = IVar fc (f nm)
    map f (IPi fc rig info nm a sc)
      = IPi fc rig (map (map f) info) nm (map f a) (map f sc)
    map f (ILam fc rig info nm a sc)
      = ILam fc rig (map (map f) info) nm (map f a) (map f sc)
    map f (ILet fc lhsFC rig nm ty val sc)
      = ILet fc lhsFC rig nm (map f ty) (map f val) (map f sc)
    map f (ICase fc sc ty cls)
      = ICase fc (map f sc) (map f ty) (map (map f) cls)
    map f (ILocal fc ds sc)
      = ILocal fc (map (map f) ds) (map f sc)
    map f (ICaseLocal fc userN intN args sc)
      = ICaseLocal fc userN intN args (map f sc)
    map f (IUpdate fc upds rec)
      = IUpdate fc (map (map f) upds) (map f rec)
    map f (IApp fc fn t)
      = IApp fc (map f fn) (map f t)
    map f (IAutoApp fc fn t)
      = IAutoApp fc (map f fn) (map f t)
    map f (INamedApp fc fn nm t)
      = INamedApp fc (map f fn) nm (map f t)
    map f (IWithApp fc fn t)
      = IWithApp fc (map f fn) (map f t)
    map f (ISearch fc n)
      = ISearch fc n
    map f (IAlternative fc alt ts)
      = IAlternative fc (map f alt) (map (map f) ts)
    map f (IRewrite fc e t)
      = IRewrite fc (map f e) (map f t)
    map f (ICoerced fc e)
      = ICoerced fc (map f e)
    map f (IBindHere fc bd t)
      = IBindHere fc bd (map f t)
    map f (IBindVar fc str)
      = IBindVar fc str
    map f (IAs fc nmFC side nm t)
      = IAs fc nmFC side nm (map f t)
    map f (IMustUnify fc reason t)
      = IMustUnify fc reason (map f t)
    map f (IDelayed fc reason t)
      = IDelayed fc reason (map f t)
    map f (IDelay fc t)
      = IDelay fc (map f t)
    map f (IForce fc t)
      = IForce fc (map f t)
    map f (IQuote fc t)
      = IQuote fc (map f t)
    map f (IQuoteName fc nm)
      = IQuoteName fc nm
    map f (IQuoteDecl fc ds)
      = IQuoteDecl fc (map (map f) ds)
    map f (IUnquote fc t)
      = IUnquote fc (map f t)
    map f (IRunElab fc t)
      = IRunElab fc (map f t)
    map f (IPrimVal fc c)
      = IPrimVal fc c
    map f (IType fc)
      = IType fc
    map f (IHole fc str)
      = IHole fc str
    map f (IUnifyLog fc lvl t)
      = IUnifyLog fc lvl (map f t)
    map f (Implicit fc b)
      = Implicit fc b
    map f (IWithUnambigNames fc ns t)
      = IWithUnambigNames fc ns (map f t)

  export
  Functor ImpClause' where
    map f (PatClause fc lhs rhs)
      = PatClause fc (map f lhs) (map f rhs)
    map f (WithClause fc lhs rig wval prf flags xs)
      = WithClause fc (map f lhs) rig (map f wval) prf flags (map (map f) xs)
    map f (ImpossibleClause fc lhs)
      = ImpossibleClause fc (map f lhs)

  export
  Functor ImpDecl' where
    map f (IClaim fc rig vis opts ty)
      = IClaim fc rig vis (map (map f) opts) (map f ty)
    map f (IData fc vis mbtot dt)
      = IData fc vis mbtot (map f dt)
    map f (IDef fc nm cls)
      = IDef fc nm (map (map f) cls)
    map f (IParameters fc ps ds)
      = IParameters fc (map (map  {f = ImpParameter'} f) ps) (map (map f) ds)
    map f (IRecord fc cs vis mbtot rec)
      = IRecord fc cs vis mbtot (map f rec)
    map f (IFail fc msg ds)
      = IFail fc msg (map (map f) ds)
    map f (INamespace fc ns ds)
      = INamespace fc ns (map (map f) ds)
    map f (ITransform fc n lhs rhs)
      = ITransform fc n (map f lhs) (map f rhs)
    map f (IRunElabDecl fc t)
      = IRunElabDecl fc (map f t)
    map f (IPragma xs k) = IPragma xs k
    map f (ILog x) = ILog x
    map f (IBuiltin fc ty n) = IBuiltin fc ty n

  export
  Functor FnOpt' where
    map f Inline = Inline
    map f NoInline = NoInline
    map f Deprecate = Deprecate
    map f TCInline = TCInline
    map f (Hint b) = Hint b
    map f (GlobalHint b) = GlobalHint b
    map f ExternFn = ExternFn
    map f (ForeignFn ts) = ForeignFn (map (map f) ts)
    map f (ForeignExport ts) = ForeignExport (map (map f) ts)
    map f Invertible = Invertible
    map f (Totality tot) = Totality tot
    map f Macro = Macro
    map f (SpecArgs ns) = SpecArgs ns

  export
  Functor ImpTy' where
    map f (MkImpTy fc nameFC n ty)
      = MkImpTy fc nameFC n (map f ty)

  export
  Functor ImpData' where
    map f (MkImpData fc n tycon opts datacons)
      = MkImpData fc n (map f tycon) opts (map (map f) datacons)
    map f (MkImpLater fc n tycon)
      = MkImpLater fc n (map f tycon)

  export
  Functor IField' where
    map f (MkIField fc rig info n t)
      = MkIField fc rig (map (map f) info) n (map f t)

  export
  Functor ImpRecord' where
    map f (MkImpRecord fc n params conName fields)
      = MkImpRecord fc n (map (map {f = ImpParameter'} f) params)
                    conName (map (map f) fields)

  export
  Functor ImpParameter' where
    map f (nm, rig, info, t) = (nm, rig, map (map f) info, map f t)

  export
  Functor IFieldUpdate' where
    map f (ISetField path t) = ISetField path (map f t)
    map f (ISetFieldApp path t) = ISetFieldApp path (map f t)

  export
  Functor AltType' where
    map f FirstSuccess = FirstSuccess
    map f Unique = Unique
    map f (UniqueDefault t) = UniqueDefault (map f t)
