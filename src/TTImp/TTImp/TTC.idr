module TTImp.TTImp.TTC

import Core.Binary
import Core.TTC

import Core.Context
import Core.Context.TTC

import TTImp.TTImp

import Libraries.Data.NatSet
import Libraries.Data.WithDefault

%default covering

mutual
  export
  TTC RawImp where
    toBuf (IVar fc n) = do tag 0; toBuf fc; toBuf n
    toBuf (IPi fc r p n argTy retTy)
        = do tag 1; toBuf fc; toBuf r; toBuf p; toBuf n
             toBuf argTy; toBuf retTy
    toBuf (ILam fc r p n argTy scope)
        = do tag 2; toBuf fc; toBuf r; toBuf p; toBuf n;
             toBuf argTy; toBuf scope
    toBuf (ILet fc lhsFC r n nTy nVal scope)
        = do tag 3; toBuf fc; toBuf lhsFC; toBuf r; toBuf n;
             toBuf nTy; toBuf nVal; toBuf scope
    toBuf (ICase fc opts y ty xs)
        = do tag 4; toBuf fc; toBuf opts; toBuf y; toBuf ty; toBuf xs
    toBuf (ILocal fc xs sc)
        = do tag 5; toBuf fc; toBuf xs; toBuf sc
    toBuf (ICaseLocal fc _ _ _ sc)
        = toBuf sc
    toBuf (IUpdate fc fs rec)
        = do tag 6; toBuf fc; toBuf fs; toBuf rec
    toBuf (IApp fc fn arg)
        = do tag 7; toBuf fc; toBuf fn; toBuf arg
    toBuf (INamedApp fc fn y arg)
        = do tag 8; toBuf fc; toBuf fn; toBuf y; toBuf arg
    toBuf (IWithApp fc fn arg)
        = do tag 9; toBuf fc; toBuf fn; toBuf arg
    toBuf (ISearch fc depth)
        = do tag 10; toBuf fc; toBuf depth
    toBuf (IAlternative fc y xs)
        = do tag 11; toBuf fc; toBuf y; toBuf xs
    toBuf (IRewrite fc x y)
        = do tag 12; toBuf fc; toBuf x; toBuf y
    toBuf (ICoerced fc y)
        = do tag 13; toBuf fc; toBuf y

    toBuf (IBindHere fc m y)
        = do tag 14; toBuf fc; toBuf m; toBuf y
    toBuf (IBindVar fc y)
        = do tag 15; toBuf fc; toBuf y
    toBuf (IAs fc nameFC s y pattern)
        = do tag 16; toBuf fc; toBuf nameFC; toBuf s; toBuf y;
             toBuf pattern
    toBuf (IMustUnify fc r pattern)
        -- No need to record 'r', it's for type errors only
        = do tag 17; toBuf fc; toBuf pattern

    toBuf (IDelayed fc r y)
        = do tag 18; toBuf fc; toBuf r; toBuf y
    toBuf (IDelay fc t)
        = do tag 19; toBuf fc; toBuf t
    toBuf (IForce fc t)
        = do tag 20; toBuf fc; toBuf t

    toBuf (IQuote fc t)
        = do tag 21; toBuf fc; toBuf t
    toBuf (IQuoteName fc t)
        = do tag 22; toBuf fc; toBuf t
    toBuf (IQuoteDecl fc t)
        = do tag 23; toBuf fc; toBuf t
    toBuf (IUnquote fc t)
        = do tag 24; toBuf fc; toBuf t
    toBuf (IRunElab fc re t)
        = do tag 25; toBuf fc; toBuf re; toBuf t

    toBuf (IPrimVal fc y)
        = do tag 26; toBuf fc; toBuf y
    toBuf (IType fc)
        = do tag 27; toBuf fc
    toBuf (IHole fc y)
        = do tag 28; toBuf fc; toBuf y
    toBuf (IUnifyLog fc lvl x) = toBuf x

    toBuf (Implicit fc i)
        = do tag 29; toBuf fc; toBuf i
    toBuf (IWithUnambigNames fc ns rhs)
        = do tag 30; toBuf fc; toBuf ns; toBuf rhs
    toBuf (IAutoApp fc fn arg)
        = do tag 31; toBuf fc; toBuf fn; toBuf arg

    fromBuf
        = case !getTag of
               0 => do fc <- fromBuf; n <- fromBuf;
                       pure (IVar fc n)
               1 => do fc <- fromBuf;
                       r <- fromBuf; p <- fromBuf;
                       n <- fromBuf
                       argTy <- fromBuf; retTy <- fromBuf
                       pure (IPi fc r p n argTy retTy)
               2 => do fc <- fromBuf;
                       r <- fromBuf; p <- fromBuf; n <- fromBuf
                       argTy <- fromBuf; scope <- fromBuf
                       pure (ILam fc r p n argTy scope)
               3 => do fc <- fromBuf;
                       lhsFC <- fromBuf;
                       r <- fromBuf; n <- fromBuf
                       nTy <- fromBuf; nVal <- fromBuf
                       scope <- fromBuf
                       pure (ILet fc lhsFC r n nTy nVal scope)
               4 => do fc <- fromBuf; opts <- fromBuf; y <- fromBuf;
                       ty <- fromBuf; xs <- fromBuf
                       pure (ICase fc opts y ty xs)
               5 => do fc <- fromBuf;
                       xs <- fromBuf; sc <- fromBuf
                       pure (ILocal fc xs sc)
               6 => do fc <- fromBuf; fs <- fromBuf
                       rec <- fromBuf
                       pure (IUpdate fc fs rec)
               7 => do fc <- fromBuf; fn <- fromBuf
                       arg <- fromBuf
                       pure (IApp fc fn arg)
               8 => do fc <- fromBuf; fn <- fromBuf
                       y <- fromBuf; arg <- fromBuf
                       pure (INamedApp fc fn y arg)
               9 => do fc <- fromBuf; fn <- fromBuf
                       arg <- fromBuf
                       pure (IWithApp fc fn arg)
               10 => do fc <- fromBuf; depth <- fromBuf
                        pure (ISearch fc depth)
               11 => do fc <- fromBuf; y <- fromBuf
                        xs <- fromBuf
                        pure (IAlternative fc y xs)
               12 => do fc <- fromBuf; x <- fromBuf; y <- fromBuf
                        pure (IRewrite fc x y)
               13 => do fc <- fromBuf; y <- fromBuf
                        pure (ICoerced fc y)
               14 => do fc <- fromBuf; m <- fromBuf; y <- fromBuf
                        pure (IBindHere fc m y)
               15 => do fc <- fromBuf; y <- fromBuf
                        pure (IBindVar fc y)
               16 => do fc <- fromBuf; nameFC <- fromBuf
                        side <- fromBuf;
                        y <- fromBuf; pattern <- fromBuf
                        pure (IAs fc nameFC side y pattern)
               17 => do fc <- fromBuf
                        pattern <- fromBuf
                        pure (IMustUnify fc UnknownDot pattern)

               18 => do fc <- fromBuf; r <- fromBuf
                        y <- fromBuf
                        pure (IDelayed fc r y)
               19 => do fc <- fromBuf; y <- fromBuf
                        pure (IDelay fc y)
               20 => do fc <- fromBuf; y <- fromBuf
                        pure (IForce fc y)

               21 => do fc <- fromBuf; y <- fromBuf
                        pure (IQuote fc y)
               22 => do fc <- fromBuf; y <- fromBuf
                        pure (IQuoteName fc y)
               23 => do fc <- fromBuf; y <- fromBuf
                        pure (IQuoteDecl fc y)
               24 => do fc <- fromBuf; y <- fromBuf
                        pure (IUnquote fc y)
               25 => do fc <- fromBuf; re <- fromBuf; y <- fromBuf
                        pure (IRunElab fc re y)

               26 => do fc <- fromBuf; y <- fromBuf
                        pure (IPrimVal fc y)
               27 => do fc <- fromBuf
                        pure (IType fc)
               28 => do fc <- fromBuf; y <- fromBuf
                        pure (IHole fc y)
               29 => do fc <- fromBuf
                        i <- fromBuf
                        pure (Implicit fc i)
               30 => do fc <- fromBuf
                        ns <- fromBuf
                        rhs <- fromBuf
                        pure (IWithUnambigNames fc ns rhs)
               31 => do fc <- fromBuf; fn <- fromBuf
                        arg <- fromBuf
                        pure (IAutoApp fc fn arg)
               _ => corrupt "RawImp"

  export
  TTC IFieldUpdate where
    toBuf (ISetField p val)
        = do tag 0; toBuf p; toBuf val
    toBuf (ISetFieldApp p val)
        = do tag 1; toBuf p; toBuf val

    fromBuf
        = case !getTag of
               0 => do p <- fromBuf; val <- fromBuf
                       pure (ISetField p val)
               1 => do p <- fromBuf; val <- fromBuf
                       pure (ISetFieldApp p val)
               _ => corrupt "IFieldUpdate"

  export
  TTC BindMode where
    toBuf (PI r) = do tag 0; toBuf r
    toBuf PATTERN = tag 1
    toBuf NONE = tag 2
    toBuf COVERAGE = tag 3

    fromBuf
        = case !getTag of
               0 => do x <- fromBuf
                       pure (PI x)
               1 => pure PATTERN
               2 => pure NONE
               3 => pure COVERAGE
               _ => corrupt "BindMode"

  export
  TTC AltType where
    toBuf FirstSuccess = tag 0
    toBuf Unique = tag 1
    toBuf (UniqueDefault x) = do tag 2; toBuf x

    fromBuf
        = case !getTag of
               0 => pure FirstSuccess
               1 => pure Unique
               2 => do x <- fromBuf
                       pure (UniqueDefault x)
               _ => corrupt "AltType"

  export
  TTC ImpClause where
    toBuf (PatClause fc lhs rhs)
        = do tag 0; toBuf fc; toBuf lhs; toBuf rhs
    toBuf (ImpossibleClause fc lhs)
        = do tag 1; toBuf fc; toBuf lhs
    toBuf (WithClause fc lhs rig wval prf flags cs)
        = do tag 2
             toBuf fc
             toBuf lhs
             toBuf rig
             toBuf wval
             toBuf prf
             toBuf cs

    fromBuf
        = case !getTag of
               0 => do fc <- fromBuf; lhs <- fromBuf;
                       rhs <- fromBuf
                       pure (PatClause fc lhs rhs)
               1 => do fc <- fromBuf; lhs <- fromBuf;
                       pure (ImpossibleClause fc lhs)
               2 => do fc <- fromBuf; lhs <- fromBuf;
                       rig <- fromBuf; wval <- fromBuf;
                       prf <- fromBuf;
                       cs <- fromBuf
                       pure (WithClause fc lhs rig wval prf [] cs)
               _ => corrupt "ImpClause"

  export
  TTC DataOpt where
    toBuf (SearchBy ns)
        = do tag 0; toBuf ns
    toBuf NoHints = tag 1
    toBuf UniqueSearch = tag 2
    toBuf External = tag 3
    toBuf NoNewtype = tag 4

    fromBuf
        = case !getTag of
               0 => do ns <- fromBuf
                       pure (SearchBy ns)
               1 => pure NoHints
               2 => pure UniqueSearch
               3 => pure External
               4 => pure NoNewtype
               _ => corrupt "DataOpt"

  export
  TTC ImpData where
    toBuf (MkImpData fc n tycon opts cons)
        = do tag 0; toBuf fc; toBuf n; toBuf tycon; toBuf opts
             toBuf cons
    toBuf (MkImpLater fc n tycon)
        = do tag 1; toBuf fc; toBuf n; toBuf tycon

    fromBuf
        = case !getTag of
               0 => do fc <- fromBuf; n <- fromBuf;
                       tycon <- fromBuf; opts <- fromBuf
                       cons <- fromBuf
                       pure (MkImpData fc n tycon opts cons)
               1 => do fc <- fromBuf; n <- fromBuf;
                       tycon <- fromBuf
                       pure (MkImpLater fc n tycon)
               _ => corrupt "ImpData"

  export
  TTC (ImpRecordData Name) where
    toBuf (MkImpRecord header body)
        = do toBuf header; toBuf body;

    fromBuf
        = do header <- fromBuf; body <- fromBuf;
             pure (MkImpRecord header body)

  export
  TTC FnOpt where
    toBuf Inline = tag 0
    toBuf (Hint t) = do tag 1; toBuf t
    toBuf (GlobalHint t) = do tag 2; toBuf t
    toBuf ExternFn = tag 3
    toBuf (ForeignFn cs) = do tag 4; toBuf cs
    toBuf Invertible = tag 5
    toBuf (Totality Total) = tag 6
    toBuf (Totality CoveringOnly) = tag 7
    toBuf (Totality PartialOK) = tag 8
    toBuf Macro = tag 9
    toBuf (SpecArgs ns) = do tag 10; toBuf ns
    toBuf TCInline = tag 11
    toBuf NoInline = tag 12
    toBuf Unsafe = tag 13
    toBuf Deprecate = tag 14
    toBuf (ForeignExport cs) = do tag 15; toBuf cs

    fromBuf
        = case !getTag of
               0 => pure Inline
               1 => do t <- fromBuf; pure (Hint t)
               2 => do t <- fromBuf; pure (GlobalHint t)
               3 => pure ExternFn
               4 => do cs <- fromBuf; pure (ForeignFn cs)
               5 => pure Invertible
               6 => pure (Totality Total)
               7 => pure (Totality CoveringOnly)
               8 => pure (Totality PartialOK)
               9 => pure Macro
               10 => do ns <- fromBuf; pure (SpecArgs ns)
               11 => pure TCInline
               12 => pure NoInline
               13 => pure Unsafe
               14 => pure Deprecate
               15 => do cs <- fromBuf; pure (ForeignExport cs)
               _ => corrupt "FnOpt"

  export
  TTC (IClaimData Name) where
    toBuf (MkIClaimData rig vis opts type)
        = do toBuf rig; toBuf vis; toBuf opts; toBuf type
    fromBuf
        = do rig <- fromBuf
             vis <- fromBuf
             opts <- fromBuf
             type <- fromBuf
             pure $ MkIClaimData rig vis opts type

  export
  TTC ImpDecl where
    toBuf (IClaim claim)
        = do tag 0; toBuf claim
    toBuf (IData fc vis mbtot d)
        = do tag 1; toBuf fc; toBuf vis; toBuf mbtot; toBuf d
    toBuf (IDef fc n xs)
        = do tag 2; toBuf fc; toBuf n; toBuf xs
    toBuf (IParameters fc vis d)
        = do tag 3; toBuf fc; toBuf vis; toBuf d
    toBuf (IRecord fc ns vis mbtot r)
        = do tag 4; toBuf fc; toBuf ns; toBuf vis; toBuf mbtot; toBuf r
    toBuf (INamespace fc xs ds)
        = do tag 5; toBuf fc; toBuf xs; toBuf ds
    toBuf (ITransform fc n lhs rhs)
        = do tag 6; toBuf fc; toBuf n; toBuf lhs; toBuf rhs
    toBuf (IRunElabDecl fc tm)
        = do tag 7; toBuf fc; toBuf tm
    toBuf (IPragma _ _ f) = throw (InternalError "Can't write Pragma")
    toBuf (ILog n)
        = do tag 8; toBuf n
    toBuf (IBuiltin fc type name)
        = do tag 9; toBuf fc; toBuf type; toBuf name
    toBuf (IFail {})
        = pure ()

    fromBuf
        = case !getTag of
               0 => do claimData <- fromBuf
                       pure (IClaim claimData)
               1 => do fc <- fromBuf; vis <- fromBuf
                       mbtot <- fromBuf; d <- fromBuf
                       pure (IData fc vis mbtot d)
               2 => do fc <- fromBuf; n <- fromBuf
                       xs <- fromBuf
                       pure (IDef fc n xs)
               3 => do fc <- fromBuf; vis <- fromBuf
                       d <- fromBuf
                       pure (IParameters fc vis d)
               4 => do fc <- fromBuf; ns <- fromBuf;
                       vis <- fromBuf; mbtot <- fromBuf;
                       r <- fromBuf
                       pure (IRecord fc ns vis mbtot r)
               5 => do fc <- fromBuf; xs <- fromBuf
                       ds <- fromBuf
                       pure (INamespace fc xs ds)
               6 => do fc <- fromBuf; n <- fromBuf
                       lhs <- fromBuf; rhs <- fromBuf
                       pure (ITransform fc n lhs rhs)
               7 => do fc <- fromBuf; tm <- fromBuf
                       pure (IRunElabDecl fc tm)
               8 => do n <- fromBuf
                       pure (ILog n)
               9 => do fc <- fromBuf
                       type <- fromBuf
                       name <- fromBuf
                       pure (IBuiltin fc type name)
               _ => corrupt "ImpDecl"
