module TTImp.TTImp.TTC

import Core.Binary
import Core.TTC

import Core.Context
import Core.Context.TTC

import TTImp.TTImp

%default covering

mutual
  export
  TTC RawImp where
    toBuf b (IVar fc n) = do tag 0; toBuf b fc; toBuf b n
    toBuf b (IPi fc r p n argTy retTy)
        = do tag 1; toBuf b fc; toBuf b r; toBuf b p; toBuf b n
             toBuf b argTy; toBuf b retTy
    toBuf b (ILam fc r p n argTy scope)
        = do tag 2; toBuf b fc; toBuf b r; toBuf b p; toBuf b n;
             toBuf b argTy; toBuf b scope
    toBuf b (ILet fc lhsFC r n nTy nVal scope)
        = do tag 3; toBuf b fc; toBuf b lhsFC; toBuf b r; toBuf b n;
             toBuf b nTy; toBuf b nVal; toBuf b scope
    toBuf b (ICase fc y ty xs)
        = do tag 4; toBuf b fc; toBuf b y; toBuf b ty; toBuf b xs
    toBuf b (ILocal fc xs sc)
        = do tag 5; toBuf b fc; toBuf b xs; toBuf b sc
    toBuf b (ICaseLocal fc _ _ _ sc)
        = toBuf b sc
    toBuf b (IUpdate fc fs rec)
        = do tag 6; toBuf b fc; toBuf b fs; toBuf b rec
    toBuf b (IApp fc fn arg)
        = do tag 7; toBuf b fc; toBuf b fn; toBuf b arg
    toBuf b (INamedApp fc fn y arg)
        = do tag 8; toBuf b fc; toBuf b fn; toBuf b y; toBuf b arg
    toBuf b (IWithApp fc fn arg)
        = do tag 9; toBuf b fc; toBuf b fn; toBuf b arg
    toBuf b (ISearch fc depth)
        = do tag 10; toBuf b fc; toBuf b depth
    toBuf b (IAlternative fc y xs)
        = do tag 11; toBuf b fc; toBuf b y; toBuf b xs
    toBuf b (IRewrite fc x y)
        = do tag 12; toBuf b fc; toBuf b x; toBuf b y
    toBuf b (ICoerced fc y)
        = do tag 13; toBuf b fc; toBuf b y

    toBuf b (IBindHere fc m y)
        = do tag 14; toBuf b fc; toBuf b m; toBuf b y
    toBuf b (IBindVar fc y)
        = do tag 15; toBuf b fc; toBuf b y
    toBuf b (IAs fc nameFC s y pattern)
        = do tag 16; toBuf b fc; toBuf b nameFC; toBuf b s; toBuf b y;
             toBuf b pattern
    toBuf b (IMustUnify fc r pattern)
        -- No need to record 'r', it's for type errors only
        = do tag 17; toBuf b fc; toBuf b pattern

    toBuf b (IDelayed fc r y)
        = do tag 18; toBuf b fc; toBuf b r; toBuf b y
    toBuf b (IDelay fc t)
        = do tag 19; toBuf b fc; toBuf b t
    toBuf b (IForce fc t)
        = do tag 20; toBuf b fc; toBuf b t

    toBuf b (IQuote fc t)
        = do tag 21; toBuf b fc; toBuf b t
    toBuf b (IQuoteName fc t)
        = do tag 22; toBuf b fc; toBuf b t
    toBuf b (IQuoteDecl fc t)
        = do tag 23; toBuf b fc; toBuf b t
    toBuf b (IUnquote fc t)
        = do tag 24; toBuf b fc; toBuf b t
    toBuf b (IRunElab fc t)
        = do tag 25; toBuf b fc; toBuf b t

    toBuf b (IPrimVal fc y)
        = do tag 26; toBuf b fc; toBuf b y
    toBuf b (IType fc)
        = do tag 27; toBuf b fc
    toBuf b (IHole fc y)
        = do tag 28; toBuf b fc; toBuf b y
    toBuf b (IUnifyLog fc lvl x) = toBuf b x

    toBuf b (Implicit fc i)
        = do tag 29; toBuf b fc; toBuf b i
    toBuf b (IWithUnambigNames fc ns rhs)
        = do tag 30; toBuf b ns; toBuf b rhs
    toBuf b (IAutoApp fc fn arg)
        = do tag 31; toBuf b fc; toBuf b fn; toBuf b arg

    fromBuf b
        = case !getTag of
               0 => do fc <- fromBuf b; n <- fromBuf b;
                       pure (IVar fc n)
               1 => do fc <- fromBuf b;
                       r <- fromBuf b; p <- fromBuf b;
                       n <- fromBuf b
                       argTy <- fromBuf b; retTy <- fromBuf b
                       pure (IPi fc r p n argTy retTy)
               2 => do fc <- fromBuf b;
                       r <- fromBuf b; p <- fromBuf b; n <- fromBuf b
                       argTy <- fromBuf b; scope <- fromBuf b
                       pure (ILam fc r p n argTy scope)
               3 => do fc <- fromBuf b;
                       lhsFC <- fromBuf b;
                       r <- fromBuf b; n <- fromBuf b
                       nTy <- fromBuf b; nVal <- fromBuf b
                       scope <- fromBuf b
                       pure (ILet fc lhsFC r n nTy nVal scope)
               4 => do fc <- fromBuf b; y <- fromBuf b;
                       ty <- fromBuf b; xs <- fromBuf b
                       pure (ICase fc y ty xs)
               5 => do fc <- fromBuf b;
                       xs <- fromBuf b; sc <- fromBuf b
                       pure (ILocal fc xs sc)
               6 => do fc <- fromBuf b; fs <- fromBuf b
                       rec <- fromBuf b
                       pure (IUpdate fc fs rec)
               7 => do fc <- fromBuf b; fn <- fromBuf b
                       arg <- fromBuf b
                       pure (IApp fc fn arg)
               8 => do fc <- fromBuf b; fn <- fromBuf b
                       y <- fromBuf b; arg <- fromBuf b
                       pure (INamedApp fc fn y arg)
               9 => do fc <- fromBuf b; fn <- fromBuf b
                       arg <- fromBuf b
                       pure (IWithApp fc fn arg)
               10 => do fc <- fromBuf b; depth <- fromBuf b
                        pure (ISearch fc depth)
               11 => do fc <- fromBuf b; y <- fromBuf b
                        xs <- fromBuf b
                        pure (IAlternative fc y xs)
               12 => do fc <- fromBuf b; x <- fromBuf b; y <- fromBuf b
                        pure (IRewrite fc x y)
               13 => do fc <- fromBuf b; y <- fromBuf b
                        pure (ICoerced fc y)
               14 => do fc <- fromBuf b; m <- fromBuf b; y <- fromBuf b
                        pure (IBindHere fc m y)
               15 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IBindVar fc y)
               16 => do fc <- fromBuf b; nameFC <- fromBuf b
                        side <- fromBuf b;
                        y <- fromBuf b; pattern <- fromBuf b
                        pure (IAs fc nameFC side y pattern)
               17 => do fc <- fromBuf b
                        pattern <- fromBuf b
                        pure (IMustUnify fc UnknownDot pattern)

               18 => do fc <- fromBuf b; r <- fromBuf b
                        y <- fromBuf b
                        pure (IDelayed fc r y)
               19 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IDelay fc y)
               20 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IForce fc y)

               21 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IQuote fc y)
               22 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IQuoteName fc y)
               23 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IQuoteDecl fc y)
               24 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IUnquote fc y)
               25 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IRunElab fc y)

               26 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IPrimVal fc y)
               27 => do fc <- fromBuf b
                        pure (IType fc)
               28 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IHole fc y)
               29 => do fc <- fromBuf b
                        i <- fromBuf b
                        pure (Implicit fc i)
               30 => do fc <- fromBuf b
                        ns <- fromBuf b
                        rhs <- fromBuf b
                        pure (IWithUnambigNames fc ns rhs)
               31 => do fc <- fromBuf b; fn <- fromBuf b
                        arg <- fromBuf b
                        pure (IAutoApp fc fn arg)
               _ => corrupt "RawImp"

  export
  TTC IFieldUpdate where
    toBuf b (ISetField p val)
        = do tag 0; toBuf b p; toBuf b val
    toBuf b (ISetFieldApp p val)
        = do tag 1; toBuf b p; toBuf b val

    fromBuf b
        = case !getTag of
               0 => do p <- fromBuf b; val <- fromBuf b
                       pure (ISetField p val)
               1 => do p <- fromBuf b; val <- fromBuf b
                       pure (ISetFieldApp p val)
               _ => corrupt "IFieldUpdate"

  export
  TTC BindMode where
    toBuf b (PI r) = do tag 0; toBuf b r
    toBuf b PATTERN = tag 1
    toBuf b NONE = tag 2
    toBuf b COVERAGE = tag 3

    fromBuf b
        = case !getTag of
               0 => do x <- fromBuf b
                       pure (PI x)
               1 => pure PATTERN
               2 => pure NONE
               3 => pure COVERAGE
               _ => corrupt "BindMode"

  export
  TTC AltType where
    toBuf b FirstSuccess = tag 0
    toBuf b Unique = tag 1
    toBuf b (UniqueDefault x) = do tag 2; toBuf b x

    fromBuf b
        = case !getTag of
               0 => pure FirstSuccess
               1 => pure Unique
               2 => do x <- fromBuf b
                       pure (UniqueDefault x)
               _ => corrupt "AltType"

  export
  TTC ImpTy where
    toBuf b (MkImpTy fc nameFC n ty)
        = do toBuf b fc; toBuf b nameFC; toBuf b n; toBuf b ty
    fromBuf b
        = do fc <- fromBuf b; nameFC <- fromBuf b; n <- fromBuf b; ty <- fromBuf b
             pure (MkImpTy fc nameFC n ty)

  export
  TTC ImpClause where
    toBuf b (PatClause fc lhs rhs)
        = do tag 0; toBuf b fc; toBuf b lhs; toBuf b rhs
    toBuf b (ImpossibleClause fc lhs)
        = do tag 1; toBuf b fc; toBuf b lhs
    toBuf b (WithClause fc lhs rig wval prf flags cs)
        = do tag 2
             toBuf b fc
             toBuf b lhs
             toBuf b rig
             toBuf b wval
             toBuf b prf
             toBuf b cs

    fromBuf b
        = case !getTag of
               0 => do fc <- fromBuf b; lhs <- fromBuf b;
                       rhs <- fromBuf b
                       pure (PatClause fc lhs rhs)
               1 => do fc <- fromBuf b; lhs <- fromBuf b;
                       pure (ImpossibleClause fc lhs)
               2 => do fc <- fromBuf b; lhs <- fromBuf b;
                       rig <- fromBuf b; wval <- fromBuf b;
                       prf <- fromBuf b;
                       cs <- fromBuf b
                       pure (WithClause fc lhs rig wval prf [] cs)
               _ => corrupt "ImpClause"

  export
  TTC DataOpt where
    toBuf b (SearchBy ns)
        = do tag 0; toBuf b ns
    toBuf b NoHints = tag 1
    toBuf b UniqueSearch = tag 2
    toBuf b External = tag 3
    toBuf b NoNewtype = tag 4

    fromBuf b
        = case !getTag of
               0 => do ns <- fromBuf b
                       pure (SearchBy ns)
               1 => pure NoHints
               2 => pure UniqueSearch
               3 => pure External
               4 => pure NoNewtype
               _ => corrupt "DataOpt"

  export
  TTC ImpData where
    toBuf b (MkImpData fc n tycon opts cons)
        = do tag 0; toBuf b fc; toBuf b n; toBuf b tycon; toBuf b opts
             toBuf b cons
    toBuf b (MkImpLater fc n tycon)
        = do tag 1; toBuf b fc; toBuf b n; toBuf b tycon

    fromBuf b
        = case !getTag of
               0 => do fc <- fromBuf b; n <- fromBuf b;
                       tycon <- fromBuf b; opts <- fromBuf b
                       cons <- fromBuf b
                       pure (MkImpData fc n tycon opts cons)
               1 => do fc <- fromBuf b; n <- fromBuf b;
                       tycon <- fromBuf b
                       pure (MkImpLater fc n tycon)
               _ => corrupt "ImpData"

  export
  TTC IField where
    toBuf b (MkIField fc c p n ty)
        = do toBuf b fc; toBuf b c; toBuf b p; toBuf b n; toBuf b ty

    fromBuf b
        = do fc <- fromBuf b; c <- fromBuf b; p <- fromBuf b
             n <- fromBuf b; ty <- fromBuf b
             pure (MkIField fc c p n ty)

  export
  TTC ImpRecord where
    toBuf b (MkImpRecord fc n ps con fs)
        = do toBuf b fc; toBuf b n; toBuf b ps; toBuf b con; toBuf b fs

    fromBuf b
        = do fc <- fromBuf b; n <- fromBuf b; ps <- fromBuf b
             con <- fromBuf b; fs <- fromBuf b
             pure (MkImpRecord fc n ps con fs)

  export
  TTC FnOpt where
    toBuf b Inline = tag 0
    toBuf b NoInline = tag 12
    toBuf b TCInline = tag 11
    toBuf b Deprecate = tag 14
    toBuf b (Hint t) = do tag 1; toBuf b t
    toBuf b (GlobalHint t) = do tag 2; toBuf b t
    toBuf b ExternFn = tag 3
    toBuf b (ForeignFn cs) = do tag 4; toBuf b cs
    toBuf b (ForeignExport cs) = do tag 15; toBuf b cs
    toBuf b Invertible = tag 5
    toBuf b (Totality Total) = tag 6
    toBuf b (Totality CoveringOnly) = tag 7
    toBuf b (Totality PartialOK) = tag 8
    toBuf b Macro = tag 9
    toBuf b (SpecArgs ns) = do tag 10; toBuf b ns

    fromBuf b
        = case !getTag of
               0 => pure Inline
               1 => do t <- fromBuf b; pure (Hint t)
               2 => do t <- fromBuf b; pure (GlobalHint t)
               3 => pure ExternFn
               4 => do cs <- fromBuf b; pure (ForeignFn cs)
               5 => pure Invertible
               6 => pure (Totality Total)
               7 => pure (Totality CoveringOnly)
               8 => pure (Totality PartialOK)
               9 => pure Macro
               10 => do ns <- fromBuf b; pure (SpecArgs ns)
               11 => pure TCInline
               12 => pure NoInline
               14 => pure Deprecate
               15 => do cs <- fromBuf b; pure (ForeignExport cs)
               _ => corrupt "FnOpt"

  export
  TTC ImpDecl where
    toBuf b (IClaim fc c vis xs d)
        = do tag 0; toBuf b fc; toBuf b c; toBuf b vis; toBuf b xs; toBuf b d
    toBuf b (IData fc vis mbtot d)
        = do tag 1; toBuf b fc; toBuf b vis; toBuf b mbtot; toBuf b d
    toBuf b (IDef fc n xs)
        = do tag 2; toBuf b fc; toBuf b n; toBuf b xs
    toBuf b (IParameters fc vis d)
        = do tag 3; toBuf b fc; toBuf b vis; toBuf b d
    toBuf b (IRecord fc ns vis mbtot r)
        = do tag 4; toBuf b fc; toBuf b ns; toBuf b vis; toBuf b mbtot; toBuf b r
    toBuf b (INamespace fc xs ds)
        = do tag 5; toBuf b fc; toBuf b xs; toBuf b ds
    toBuf b (ITransform fc n lhs rhs)
        = do tag 6; toBuf b fc; toBuf b n; toBuf b lhs; toBuf b rhs
    toBuf b (IRunElabDecl fc tm)
        = do tag 7; toBuf b fc; toBuf b tm
    toBuf b (IPragma _ f) = throw (InternalError "Can't write Pragma")
    toBuf b (ILog n)
        = do tag 8; toBuf b n
    toBuf b (IBuiltin fc type name)
        = do tag 9; toBuf b fc; toBuf b type; toBuf b name
    toBuf b (IFail _ _ _)
        = pure ()

    fromBuf b
        = case !getTag of
               0 => do fc <- fromBuf b; c <- fromBuf b
                       vis <- fromBuf b;
                       xs <- fromBuf b; d <- fromBuf b
                       pure (IClaim fc c vis xs d)
               1 => do fc <- fromBuf b; vis <- fromBuf b
                       mbtot <- fromBuf b; d <- fromBuf b
                       pure (IData fc vis mbtot d)
               2 => do fc <- fromBuf b; n <- fromBuf b
                       xs <- fromBuf b
                       pure (IDef fc n xs)
               3 => do fc <- fromBuf b; vis <- fromBuf b
                       d <- fromBuf b
                       pure (IParameters fc vis d)
               4 => do fc <- fromBuf b; ns <- fromBuf b;
                       vis <- fromBuf b; mbtot <- fromBuf b;
                       r <- fromBuf b
                       pure (IRecord fc ns vis mbtot r)
               5 => do fc <- fromBuf b; xs <- fromBuf b
                       ds <- fromBuf b
                       pure (INamespace fc xs ds)
               6 => do fc <- fromBuf b; n <- fromBuf b
                       lhs <- fromBuf b; rhs <- fromBuf b
                       pure (ITransform fc n lhs rhs)
               7 => do fc <- fromBuf b; tm <- fromBuf b
                       pure (IRunElabDecl fc tm)
               8 => do n <- fromBuf b
                       pure (ILog n)
               9 => do fc <- fromBuf b
                       type <- fromBuf b
                       name <- fromBuf b
                       pure (IBuiltin fc type name)
               _ => corrupt "ImpDecl"
