module TTImp.TTImp.Traversals

import Core.TT
import TTImp.TTImp

%default total

parameters (f : RawImp' nm -> RawImp' nm)

  export
  mapTTImp :RawImp' nm -> RawImp' nm

  export
  mapPiInfo : PiInfo (RawImp' nm) -> PiInfo (RawImp' nm)
  mapPiInfo Implicit = Implicit
  mapPiInfo Explicit = Explicit
  mapPiInfo AutoImplicit = AutoImplicit
  mapPiInfo (DefImplicit t) = DefImplicit (mapTTImp t)

  export
  mapImpClause : ImpClause' nm -> ImpClause' nm
  mapImpClause (PatClause fc lhs rhs) = PatClause fc (mapTTImp lhs) (mapTTImp rhs)
  mapImpClause (WithClause fc lhs rig wval prf flags cls)
    = WithClause fc (mapTTImp lhs) rig (mapTTImp wval) prf flags (assert_total $ map mapImpClause cls)
  mapImpClause (ImpossibleClause fc lhs) = ImpossibleClause fc (mapTTImp lhs)

  export
  mapImpTy : ImpTy' nm -> ImpTy' nm
  mapImpTy (MkImpTy fc nameFC n ty) = MkImpTy fc nameFC n (mapTTImp ty)

  export
  mapFnOpt : FnOpt' nm -> FnOpt' nm
  mapFnOpt Inline = Inline
  mapFnOpt NoInline = NoInline
  mapFnOpt Deprecate = Deprecate
  mapFnOpt TCInline = TCInline
  mapFnOpt (Hint b) = Hint b
  mapFnOpt (GlobalHint b) = GlobalHint b
  mapFnOpt ExternFn = ExternFn
  mapFnOpt (ForeignFn ts) = ForeignFn (map mapTTImp ts)
  mapFnOpt (ForeignExport ts) = ForeignExport (map mapTTImp ts)
  mapFnOpt Invertible = Invertible
  mapFnOpt (Totality treq) = Totality treq
  mapFnOpt Macro = Macro
  mapFnOpt (SpecArgs ns) = SpecArgs ns

  export
  mapImpData : ImpData' nm -> ImpData' nm
  mapImpData (MkImpData fc n tycon opts datacons)
    = MkImpData fc n (mapTTImp tycon) opts (map mapImpTy datacons)
  mapImpData (MkImpLater fc n tycon) = MkImpLater fc n (mapTTImp tycon)

  export
  mapIField : IField' nm -> IField' nm
  mapIField (MkIField fc rig pinfo n t) = MkIField fc rig (mapPiInfo pinfo) n (mapTTImp t)

  export
  mapImpRecord : ImpRecord' nm -> ImpRecord' nm
  mapImpRecord (MkImpRecord fc n params conName fields)
    = MkImpRecord fc n (map (map $ map $ bimap mapPiInfo mapTTImp) params) conName (map mapIField fields)

  export
  mapImpDecl : ImpDecl' nm -> ImpDecl' nm
  mapImpDecl (IClaim fc rig vis opts ty)
    = IClaim fc rig vis (map mapFnOpt opts) (mapImpTy ty)
  mapImpDecl (IData fc vis mtreq dat) = IData fc vis mtreq (mapImpData dat)
  mapImpDecl (IDef fc n cls) = IDef fc n (map mapImpClause cls)
  mapImpDecl (IParameters fc params xs) = IParameters fc params (assert_total $ map mapImpDecl xs)
  mapImpDecl (IRecord fc mstr x y rec) = IRecord fc mstr x y (mapImpRecord rec)
  mapImpDecl (IFail fc mstr xs) = IFail fc mstr (assert_total $ map mapImpDecl xs)
  mapImpDecl (INamespace fc mi xs) = INamespace fc mi (assert_total $ map mapImpDecl xs)
  mapImpDecl (ITransform fc n t u) = ITransform fc n (mapTTImp t) (mapTTImp u)
  mapImpDecl (IRunElabDecl fc t) = IRunElabDecl fc (mapTTImp t)
  mapImpDecl (IPragma ns g) = IPragma ns g
  mapImpDecl (ILog x) = ILog x
  mapImpDecl (IBuiltin fc x n) = IBuiltin fc x n

  export
  mapIFieldUpdate : IFieldUpdate' nm -> IFieldUpdate' nm
  mapIFieldUpdate (ISetField path t) = ISetField path (mapTTImp t)
  mapIFieldUpdate (ISetFieldApp path t) = ISetFieldApp path (mapTTImp t)

  export
  mapAltType : AltType' nm -> AltType' nm
  mapAltType FirstSuccess = FirstSuccess
  mapAltType Unique = Unique
  mapAltType (UniqueDefault t) = UniqueDefault (mapTTImp t)

  mapTTImp t@(IVar _ _) = f t
  mapTTImp (IPi fc rig pinfo x argTy retTy)
    = f $ IPi fc rig (mapPiInfo pinfo) x (mapTTImp argTy) (mapTTImp retTy)
  mapTTImp (ILam fc rig pinfo x argTy lamTy)
    = f $ ILam fc rig (mapPiInfo pinfo) x (mapTTImp argTy) (mapTTImp lamTy)
  mapTTImp (ILet fc lhsFC rig n nTy nVal scope)
    = f $ ILet fc lhsFC rig n (mapTTImp nTy) (mapTTImp nVal) (mapTTImp scope)
  mapTTImp (ICase fc t ty cls)
    = f $ ICase fc (mapTTImp t) (mapTTImp ty) (assert_total $ map mapImpClause cls)
  mapTTImp (ILocal fc xs t)
    = f $ ILocal fc (assert_total $ map mapImpDecl xs) (mapTTImp t)
  mapTTImp (ICaseLocal fc unm inm args t) = f $ ICaseLocal fc unm inm args (mapTTImp t)
  mapTTImp (IUpdate fc upds t) = f $ IUpdate fc (assert_total map mapIFieldUpdate upds) (mapTTImp t)
  mapTTImp (IApp fc t u) = f $ IApp fc (mapTTImp t) (mapTTImp u)
  mapTTImp (IAutoApp fc t u) = f $ IAutoApp fc (mapTTImp t) (mapTTImp u)
  mapTTImp (INamedApp fc t n u) = f $ INamedApp fc (mapTTImp t) n (mapTTImp u)
  mapTTImp (IWithApp fc t u) = f $ IWithApp fc (mapTTImp t) (mapTTImp u)
  mapTTImp (ISearch fc depth) = f $ ISearch fc depth
  mapTTImp (IAlternative fc alt ts) = f $ IAlternative fc (mapAltType alt) (assert_total map mapTTImp ts)
  mapTTImp (IRewrite fc t u) = f $ IRewrite fc (mapTTImp t) (mapTTImp u)
  mapTTImp (ICoerced fc t) = f $ ICoerced fc (mapTTImp t)
  mapTTImp (IBindHere fc bm t) = f $ IBindHere fc bm (mapTTImp t)
  mapTTImp (IBindVar fc str) = f $ IBindVar fc str
  mapTTImp (IAs fc nameFC side n t) = f $ IAs fc nameFC side n (mapTTImp t)
  mapTTImp (IMustUnify fc x t) = f $ IMustUnify fc x (mapTTImp t)
  mapTTImp (IDelayed fc lz t) = f $ IDelayed fc lz (mapTTImp t)
  mapTTImp (IDelay fc t) = f $ IDelay fc (mapTTImp t)
  mapTTImp (IForce fc t) = f $ IForce fc (mapTTImp t)
  mapTTImp (IQuote fc t) = f $ IQuote fc (mapTTImp t)
  mapTTImp (IQuoteName fc n) = f $ IQuoteName fc n
  mapTTImp (IQuoteDecl fc xs) = f $ IQuoteDecl fc (assert_total $ map mapImpDecl xs)
  mapTTImp (IUnquote fc t) = f $ IUnquote fc (mapTTImp t)
  mapTTImp (IRunElab fc t) = f $ IRunElab fc (mapTTImp t)
  mapTTImp (IPrimVal fc c) = f $ IPrimVal fc c
  mapTTImp (IType fc) = f $ IType fc
  mapTTImp (IHole fc str) = f $ IHole fc str
  mapTTImp (IUnifyLog fc x t) = f $ IUnifyLog fc x (mapTTImp t)
  mapTTImp (Implicit fc bindIfUnsolved) = f $ Implicit fc bindIfUnsolved
  mapTTImp (IWithUnambigNames fc xs t) = f $ IWithUnambigNames fc xs (mapTTImp t)
