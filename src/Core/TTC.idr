module Core.TTC

import Core.CaseTree
import Core.CompileExpr
import Core.Context
import Core.Core
import Core.Env
import Core.FC
import Core.Name
import Core.Options
import Core.TT

import Data.NameMap
import Data.Vect

import Utils.Binary

%default covering

export
TTC FC where
  toBuf b (MkFC file startPos endPos)
      = do tag 0; toBuf b file; toBuf b startPos; toBuf b endPos
  toBuf b EmptyFC = tag 1

  fromBuf b
      = case !getTag of
             0 => do f <- fromBuf b;
                     s <- fromBuf b; e <- fromBuf b
                     pure (MkFC f s e)
             1 => pure EmptyFC
             _ => corrupt "FC"
export
TTC Namespace where
  toBuf b = toBuf b . unsafeUnfoldNamespace
  fromBuf = Core.map unsafeFoldNamespace . fromBuf

export
TTC ModuleIdent where
  toBuf b = toBuf b . unsafeUnfoldModuleIdent
  fromBuf = Core.map unsafeFoldModuleIdent . fromBuf

export
TTC Name where
  toBuf b (NS xs x) = do tag 0; toBuf b xs; toBuf b x
  toBuf b (UN x) = do tag 1; toBuf b x
  toBuf b (MN x y) = do tag 2; toBuf b x; toBuf b y
  toBuf b (PV x y) = do tag 3; toBuf b x; toBuf b y
  toBuf b (DN x y) = do tag 4; toBuf b x; toBuf b y
  toBuf b (RF x) = do tag 5; toBuf b x
  toBuf b (Nested x y) = do tag 6; toBuf b x; toBuf b y
  toBuf b (CaseBlock x y) = do tag 7; toBuf b x; toBuf b y
  toBuf b (WithBlock x y) = do tag 8; toBuf b x; toBuf b y
  toBuf b (Resolved x)
      = throw (InternalError ("Can't write resolved name " ++ show x))

  fromBuf b
      = case !getTag of
             0 => do xs <- fromBuf b
                     x <- fromBuf b
                     pure (NS xs x)
             1 => do x <- fromBuf b
                     pure (UN x)
             2 => do x <- fromBuf b
                     y <- fromBuf b
                     pure (MN x y)
             3 => do x <- fromBuf b
                     y <- fromBuf b
                     pure (PV x y)
             4 => do x <- fromBuf b
                     y <- fromBuf b
                     pure (DN x y)
             5 => do x <- fromBuf b
                     pure (RF x)
             6 => do x <- fromBuf b
                     y <- fromBuf b
                     pure (Nested x y)
             7 => do x <- fromBuf b
                     y <- fromBuf b
                     pure (CaseBlock x y)
             8 => do x <- fromBuf b
                     y <- fromBuf b
                     pure (WithBlock x y)
             _ => corrupt "Name"

export
TTC RigCount where
  toBuf b = elimSemi
              (tag 0)
              (tag 1)
              (const $ tag 2)

  fromBuf b
      = case !getTag of
             0 => pure erased
             1 => pure linear
             2 => pure top
             _ => corrupt "RigCount"

export
TTC t => TTC (PiInfo t) where
  toBuf b Implicit = tag 0
  toBuf b Explicit = tag 1
  toBuf b AutoImplicit = tag 2
  toBuf b (DefImplicit r) = do tag 3; toBuf b r

  fromBuf b
      = case !getTag of
             0 => pure Implicit
             1 => pure Explicit
             2 => pure AutoImplicit
             3 => do t <- fromBuf b; pure (DefImplicit t)
             _ => corrupt "PiInfo"

export
TTC Constant where
  toBuf b (I x) = do tag 0; toBuf b x
  toBuf b (BI x) = do tag 1; toBuf b x
  toBuf b (B8 x) = do tag 2; toBuf b x
  toBuf b (B16 x) = do tag 3; toBuf b x
  toBuf b (B32 x) = do tag 4; toBuf b x
  toBuf b (B64 x) = do tag 5; toBuf b x
  toBuf b (Str x) = do tag 6; toBuf b x
  toBuf b (Ch x) = do tag 7; toBuf b x
  toBuf b (Db x) = do tag 8; toBuf b x

  toBuf b WorldVal = tag 9
  toBuf b IntType = tag 10
  toBuf b IntegerType = tag 11
  toBuf b Bits8Type = tag 12
  toBuf b Bits16Type = tag 13
  toBuf b Bits32Type = tag 14
  toBuf b Bits64Type = tag 15
  toBuf b StringType = tag 16
  toBuf b CharType = tag 17
  toBuf b DoubleType = tag 18
  toBuf b WorldType = tag 19

  fromBuf b
      = case !getTag of
             0 => do x <- fromBuf b; pure (I x)
             1 => do x <- fromBuf b; pure (BI x)
             2 => do x <- fromBuf b; pure (B8 x)
             3 => do x <- fromBuf b; pure (B16 x)
             4 => do x <- fromBuf b; pure (B32 x)
             5 => do x <- fromBuf b; pure (B64 x)
             6 => do x <- fromBuf b; pure (Str x)
             7 => do x <- fromBuf b; pure (Ch x)
             8 => do x <- fromBuf b; pure (Db x)
             9 => pure WorldVal
             10 => pure IntType
             11 => pure IntegerType
             12 => pure Bits8Type
             13 => pure Bits16Type
             14 => pure Bits32Type
             15 => pure Bits64Type
             16 => pure StringType
             17 => pure CharType
             18 => pure DoubleType
             19 => pure WorldType
             _ => corrupt "Constant"

export
TTC LazyReason where
  toBuf b LInf = tag 0
  toBuf b LLazy = tag 1
  toBuf b LUnknown = tag 2

  fromBuf b
      = case !getTag of
             0 => pure LInf
             1 => pure LLazy
             2 => pure LUnknown
             _ => corrupt "LazyReason"

export
TTC NameType where
  toBuf b Bound = tag 0
  toBuf b Func = tag 1
  toBuf b (DataCon t arity) = do tag 2; toBuf b t; toBuf b arity
  toBuf b (TyCon t arity) = do tag 3; toBuf b t; toBuf b arity

  fromBuf b
      = case !getTag of
             0 => pure Bound
             1 => pure Func
             2 => do x <- fromBuf b; y <- fromBuf b; pure (DataCon x y)
             3 => do x <- fromBuf b; y <- fromBuf b; pure (TyCon x y)
             _ => corrupt "NameType"

-- Assumption is that it was type safe when we wrote it out, so believe_me
-- to rebuild proofs is fine.
-- We're just making up the implicit arguments - this is only fine at run
-- time because those arguments get erased!
-- (Indeed, we're expecting the whole IsVar proof to be erased because
-- we have the idx...)
mkPrf : (idx : Nat) -> IsVar n idx ns
mkPrf {n} {ns} Z = believe_me (First {n} {ns = n :: ns})
mkPrf {n} {ns} (S k) = believe_me (Later {m=n} (mkPrf {n} {ns} k))

getName : (idx : Nat) -> List Name -> Maybe Name
getName Z (x :: xs) = Just x
getName (S k) (x :: xs) = getName k xs
getName _ [] = Nothing

mutual
  export
  {vars : _} -> TTC (Binder (Term vars)) where
    toBuf b (Lam _ c x ty) = do tag 0; toBuf b c; toBuf b x; toBuf b ty
    toBuf b (Let _ c val ty) = do tag 1; toBuf b c; toBuf b val -- ; toBuf b ty
    toBuf b (Pi _ c x ty) = do tag 2; toBuf b c; toBuf b x; toBuf b ty
    toBuf b (PVar _ c p ty) = do tag 3; toBuf b c; toBuf b p; toBuf b ty
    toBuf b (PLet _ c val ty) = do tag 4; toBuf b c; toBuf b val -- ; toBuf b ty
    toBuf b (PVTy _ c ty) = do tag 5; toBuf b c -- ; toBuf b ty

    fromBuf b
        = case !getTag of
               0 => do c <- fromBuf b; x <- fromBuf b; ty <- fromBuf b; pure (Lam emptyFC c x ty)
               1 => do c <- fromBuf b; x <- fromBuf b; pure (Let emptyFC c x (Erased emptyFC False))
               2 => do c <- fromBuf b; x <- fromBuf b; y <- fromBuf b; pure (Pi emptyFC c x y)
               3 => do c <- fromBuf b; p <- fromBuf b; ty <- fromBuf b; pure (PVar emptyFC c p ty)
               4 => do c <- fromBuf b; x <- fromBuf b; pure (PLet emptyFC c x (Erased emptyFC False))
               5 => do c <- fromBuf b; pure (PVTy emptyFC c (Erased emptyFC False))
               _ => corrupt "Binder"

  export
  TTC UseSide where
    toBuf b UseLeft = tag 0
    toBuf b UseRight = tag 1

    fromBuf b
        = case !getTag of
               0 => pure UseLeft
               1 => pure UseRight
               _ => corrupt "UseSide"


  export
  {vars : _} -> TTC (Term vars) where
    toBuf b (Local {name} fc c idx y)
        = if idx < 244
             then do tag (12 + cast idx)
                     toBuf b c
             else do tag 0
                     toBuf b c
                     toBuf b idx
    toBuf b (Ref fc nt name)
        = do tag 1;
             toBuf b nt; toBuf b name
    toBuf b (Meta fc n i xs)
        = do tag 2;
             toBuf b n; toBuf b xs
    toBuf b (Bind fc x bnd scope)
        = do tag 3;
             toBuf b x;
             toBuf b bnd; toBuf b scope
    toBuf b (App fc fn arg)
        = do tag 4;
             toBuf b fn; toBuf b arg
--              let (fn, args) = getFnArgs (App fc fn arg)
--              toBuf b fn; -- toBuf b p;
--              toBuf b args
    toBuf b (As fc s as tm)
        = do tag 5;
             toBuf b as; toBuf b s; toBuf b tm
    toBuf b (TDelayed fc r tm)
        = do tag 6;
             toBuf b r; toBuf b tm
    toBuf b (TDelay fc r ty tm)
        = do tag 7;
             toBuf b r; toBuf b ty; toBuf b tm
    toBuf b (TForce fc r tm)
        = do tag 8;
             toBuf b r; toBuf b tm
    toBuf b (PrimVal fc c)
        = do tag 9;
             toBuf b c
    toBuf b (Erased fc _)
        = tag 10
    toBuf b (TType fc)
        = tag 11

    fromBuf {vars} b
        = case !getTag of
               0 => do c <- fromBuf b
                       idx <- fromBuf b
                       name <- maybe (corrupt "Term") pure
                                     (getName idx vars)
                       pure (Local {name} emptyFC c idx (mkPrf idx))
               1 => do nt <- fromBuf b; name <- fromBuf b
                       pure (Ref emptyFC nt name)
               2 => do n <- fromBuf b
                       xs <- fromBuf b
                       pure (Meta emptyFC n 0 xs) -- needs resolving
               3 => do x <- fromBuf b
                       bnd <- fromBuf b; scope <- fromBuf b
                       pure (Bind emptyFC x bnd scope)
               4 => do fn <- fromBuf b
                       arg <- fromBuf b
                       pure (App emptyFC fn arg)
               5 => do as <- fromBuf b; s <- fromBuf b; tm <- fromBuf b
                       pure (As emptyFC s as tm)
               6 => do lr <- fromBuf b; tm <- fromBuf b
                       pure (TDelayed emptyFC lr tm)
               7 => do lr <- fromBuf b;
                       ty <- fromBuf b; tm <- fromBuf b
                       pure (TDelay emptyFC lr ty tm)
               8 => do lr <- fromBuf b; tm <- fromBuf b
                       pure (TForce emptyFC lr tm)
               9 => do c <- fromBuf b
                       pure (PrimVal emptyFC c)
               10 => pure (Erased emptyFC False)
               11 => pure (TType emptyFC)
               idxp => do c <- fromBuf b
                          let idx : Nat = fromInteger (cast (idxp - 12))
                          let Just name = getName idx vars
                              | Nothing => corrupt "Term"
                          pure (Local {name} emptyFC c idx (mkPrf idx))

export
TTC Pat where
  toBuf b (PAs fc x y)
      = do tag 0; toBuf b fc; toBuf b x; toBuf b y
  toBuf b (PCon fc x t arity xs)
      = do tag 1; toBuf b fc; toBuf b x; toBuf b t; toBuf b arity; toBuf b xs
  toBuf b (PTyCon fc x arity xs)
      = do tag 2; toBuf b fc; toBuf b x; toBuf b arity; toBuf b xs
  toBuf b (PConst fc c)
      = do tag 3; toBuf b fc; toBuf b c
  toBuf b (PArrow fc x s t)
      = do tag 4; toBuf b fc; toBuf b x; toBuf b s; toBuf b t
  toBuf b (PDelay fc x t y)
      = do tag 5; toBuf b fc; toBuf b x; toBuf b t; toBuf b y
  toBuf b (PLoc fc x)
      = do tag 6; toBuf b fc; toBuf b x
  toBuf b (PUnmatchable fc x)
      = do tag 7; toBuf b fc; toBuf b x

  fromBuf b
      = case !getTag of
             0 => do fc <- fromBuf b; x <- fromBuf b;
                     y <- fromBuf b
                     pure (PAs fc x y)
             1 => do fc <- fromBuf b; x <- fromBuf b
                     t <- fromBuf b; arity <- fromBuf b
                     xs <- fromBuf b
                     pure (PCon fc x t arity xs)
             2 => do fc <- fromBuf b; x <- fromBuf b
                     arity <- fromBuf b
                     xs <- fromBuf b
                     pure (PTyCon fc x arity xs)
             3 => do fc <- fromBuf b; c <- fromBuf b
                     pure (PConst fc c)
             4 => do fc <- fromBuf b; x <- fromBuf b
                     s <- fromBuf b; t <- fromBuf b
                     pure (PArrow fc x s t)
             5 => do fc <- fromBuf b; x <- fromBuf b;
                     t <- fromBuf b; y <- fromBuf b
                     pure (PDelay fc x t y)
             6 => do fc <- fromBuf b; x <- fromBuf b
                     pure (PLoc fc x)
             7 => do fc <- fromBuf b; x <- fromBuf b
                     pure (PUnmatchable fc x)
             _ => corrupt "Pat"

mutual
  export
  {vars : _} -> TTC (CaseTree vars) where
    toBuf b (Case {name} idx x scTy xs)
        = do tag 0; toBuf b name; toBuf b idx; toBuf b xs
    toBuf b (STerm _ x)
        = do tag 1; toBuf b x
    toBuf b (Unmatched msg)
        = do tag 2; toBuf b msg
    toBuf b Impossible = tag 3

    fromBuf b
        = case !getTag of
               0 => do name <- fromBuf b; idx <- fromBuf b
                       xs <- fromBuf b
                       pure (Case {name} idx (mkPrf idx) (Erased emptyFC False) xs)
               1 => do x <- fromBuf b
                       pure (STerm 0 x)
               2 => do msg <- fromBuf b
                       pure (Unmatched msg)
               3 => pure Impossible
               _ => corrupt "CaseTree"

  export
  {vars : _} -> TTC (CaseAlt vars) where
    toBuf b (ConCase x t args y)
        = do tag 0; toBuf b x; toBuf b t; toBuf b args; toBuf b y
    toBuf b (DelayCase ty arg y)
        = do tag 1; toBuf b ty; toBuf b arg; toBuf b y
    toBuf b (ConstCase x y)
        = do tag 2; toBuf b x; toBuf b y
    toBuf b (DefaultCase x)
        = do tag 3; toBuf b x

    fromBuf b
        = case !getTag of
               0 => do x <- fromBuf b; t <- fromBuf b
                       args <- fromBuf b; y <- fromBuf b
                       pure (ConCase x t args y)
               1 => do ty <- fromBuf b; arg <- fromBuf b; y <- fromBuf b
                       pure (DelayCase ty arg y)
               2 => do x <- fromBuf b; y <- fromBuf b
                       pure (ConstCase x y)
               3 => do x <- fromBuf b
                       pure (DefaultCase x)
               _ => corrupt "CaseAlt"

export
{vars : _} -> TTC (Env Term vars) where
  toBuf b [] = pure ()
  toBuf b ((::) bnd env)
      = do toBuf b bnd; toBuf b env

  -- Length has to correspond to length of 'vars'
  fromBuf {vars = []} b = pure Nil
  fromBuf {vars = x :: xs} b
      = do bnd <- fromBuf b
           env <- fromBuf b
           pure (bnd :: env)

export
TTC Visibility where
  toBuf b Private = tag 0
  toBuf b Export = tag 1
  toBuf b Public = tag 2

  fromBuf b
      = case !getTag of
             0 => pure Private
             1 => pure Export
             2 => pure Public
             _ => corrupt "Visibility"

export
TTC PartialReason where
  toBuf b NotStrictlyPositive = tag 0
  toBuf b (BadCall xs) = do tag 1; toBuf b xs
  toBuf b (RecPath xs) = do tag 2; toBuf b xs

  fromBuf b
      = case !getTag of
             0 => pure NotStrictlyPositive
             1 => do xs <- fromBuf b
                     pure (BadCall xs)
             2 => do xs <- fromBuf b
                     pure (RecPath xs)
             _ => corrupt "PartialReason"

export
TTC Terminating where
  toBuf b Unchecked = tag 0
  toBuf b IsTerminating = tag 1
  toBuf b (NotTerminating p) = do tag 2; toBuf b p

  fromBuf b
      = case !getTag of
             0 => pure Unchecked
             1 => pure IsTerminating
             2 => do p <- fromBuf b
                     pure (NotTerminating p)
             _ => corrupt "Terminating"

export
TTC Covering where
  toBuf b IsCovering = tag 0
  toBuf b (MissingCases ms)
      = do tag 1
           toBuf b ms
  toBuf b (NonCoveringCall ns)
      = do tag 2
           toBuf b ns

  fromBuf b
      = case !getTag of
             0 => pure IsCovering
             1 => do ms <- fromBuf b
                     pure (MissingCases ms)
             2 => do ns <- fromBuf b
                     pure (NonCoveringCall ns)
             _ => corrupt "Covering"

export
TTC Totality where
  toBuf b (MkTotality term cov) = do toBuf b term; toBuf b cov

  fromBuf b
      = do term <- fromBuf b
           cov <- fromBuf b
           pure (MkTotality term cov)

export
{n : _} -> TTC (PrimFn n) where
  toBuf b (Add ty) = do tag 0; toBuf b ty
  toBuf b (Sub ty) = do tag 1; toBuf b ty
  toBuf b (Mul ty) = do tag 2; toBuf b ty
  toBuf b (Div ty) = do tag 3; toBuf b ty
  toBuf b (Mod ty) = do tag 4; toBuf b ty
  toBuf b (Neg ty) = do tag 5; toBuf b ty
  toBuf b (ShiftL ty) = do tag 35; toBuf b ty
  toBuf b (ShiftR ty) = do tag 36; toBuf b ty
  toBuf b (BAnd ty) = do tag 37; toBuf b ty
  toBuf b (BOr ty) = do tag 38; toBuf b ty
  toBuf b (BXOr ty) = do tag 39; toBuf b ty
  toBuf b (LT ty) = do tag 6; toBuf b ty
  toBuf b (LTE ty) = do tag 7; toBuf b ty
  toBuf b (EQ ty) = do tag 8; toBuf b ty
  toBuf b (GTE ty) = do tag 9; toBuf b ty
  toBuf b (GT ty) = do tag 10; toBuf b ty
  toBuf b StrLength = tag 11
  toBuf b StrHead = tag 12
  toBuf b StrTail = tag 13
  toBuf b StrIndex = tag 14
  toBuf b StrCons = tag 15
  toBuf b StrAppend = tag 16
  toBuf b StrReverse = tag 17
  toBuf b StrSubstr = tag 18

  toBuf b DoubleExp = tag 19
  toBuf b DoubleLog = tag 20
  toBuf b DoubleSin = tag 22
  toBuf b DoubleCos = tag 23
  toBuf b DoubleTan = tag 24
  toBuf b DoubleASin = tag 25
  toBuf b DoubleACos = tag 26
  toBuf b DoubleATan = tag 27
  toBuf b DoubleSqrt = tag 32
  toBuf b DoubleFloor = tag 33
  toBuf b DoubleCeiling = tag 34

  toBuf b (Cast x y) = do tag 99; toBuf b x; toBuf b y
  toBuf b BelieveMe = tag 100
  toBuf b Crash = tag 101

  fromBuf {n} b
      = case n of
             S Z => fromBuf1
             S (S Z) => fromBuf2
             S (S (S Z)) => fromBuf3
             _ => corrupt "PrimFn"
    where
      fromBuf1 : Core (PrimFn 1)
      fromBuf1
          = case !getTag of
                 5 => do ty <- fromBuf b; pure (Neg ty)
                 11 => pure StrLength
                 12 => pure StrHead
                 13 => pure StrTail
                 17 => pure StrReverse
                 19 => pure DoubleExp
                 20 => pure DoubleLog
                 22 => pure DoubleSin
                 23 => pure DoubleCos
                 24 => pure DoubleTan
                 25 => pure DoubleASin
                 26 => pure DoubleACos
                 27 => pure DoubleATan
                 32 => pure DoubleSqrt
                 33 => pure DoubleFloor
                 34 => pure DoubleCeiling

                 99 => do x <- fromBuf b; y <- fromBuf b; pure (Cast x y)
                 _ => corrupt "PrimFn 1"

      fromBuf2 : Core (PrimFn 2)
      fromBuf2
          = case !getTag of
                 0 => do ty <- fromBuf b; pure (Add ty)
                 1 => do ty <- fromBuf b; pure (Sub ty)
                 2 => do ty <- fromBuf b; pure (Mul ty)
                 3 => do ty <- fromBuf b; pure (Div ty)
                 4 => do ty <- fromBuf b; pure (Mod ty)
                 6 => do ty <- fromBuf b; pure (LT ty)
                 7 => do ty <- fromBuf b; pure (LTE ty)
                 8 => do ty <- fromBuf b; pure (EQ ty)
                 9 => do ty <- fromBuf b; pure (GTE ty)
                 10 => do ty <- fromBuf b; pure (GT ty)
                 14 => pure StrIndex
                 15 => pure StrCons
                 16 => pure StrAppend
                 35 => do ty <- fromBuf b; pure (ShiftL ty)
                 36 => do ty <- fromBuf b; pure (ShiftR ty)
                 37 => do ty <- fromBuf b; pure (BAnd ty)
                 38 => do ty <- fromBuf b; pure (BOr ty)
                 39 => do ty <- fromBuf b; pure (BXOr ty)
                 101 => pure Crash
                 _ => corrupt "PrimFn 2"

      fromBuf3 : Core (PrimFn 3)
      fromBuf3
          = case !getTag of
                 18 => pure StrSubstr
                 100 => pure BelieveMe
                 _ => corrupt "PrimFn 3"

mutual
  export
  {vars : _} -> TTC (CExp vars) where
    toBuf b (CLocal fc {x} {idx} h) = do tag 0; toBuf b fc; toBuf b idx
    toBuf b (CRef fc n) = do tag 1; toBuf b fc; toBuf b n
    toBuf b (CLam fc x sc) = do tag 2; toBuf b fc; toBuf b x; toBuf b sc
    toBuf b (CLet fc x inl val sc) = do tag 3; toBuf b fc; toBuf b x; toBuf b inl; toBuf b val; toBuf b sc
    toBuf b (CApp fc f as) = assert_total $ do tag 4; toBuf b fc; toBuf b f; toBuf b as
    toBuf b (CCon fc t n as) = assert_total $ do tag 5; toBuf b fc; toBuf b t; toBuf b n; toBuf b as
    toBuf b (COp {arity} fc op as) = assert_total $ do tag 6; toBuf b fc; toBuf b arity; toBuf b op; toBuf b as
    toBuf b (CExtPrim fc f as) = assert_total $ do tag 7; toBuf b fc; toBuf b f; toBuf b as
    toBuf b (CForce fc x) = assert_total $ do tag 8; toBuf b fc; toBuf b x
    toBuf b (CDelay fc x) = assert_total $ do tag 9; toBuf b fc; toBuf b x
    toBuf b (CConCase fc sc alts def) = assert_total $ do tag 10; toBuf b fc; toBuf b sc; toBuf b alts; toBuf b def
    toBuf b (CConstCase fc sc alts def) = assert_total $ do tag 11; toBuf b fc; toBuf b sc; toBuf b alts; toBuf b def
    toBuf b (CPrimVal fc c) = do tag 12; toBuf b fc; toBuf b c
    toBuf b (CErased fc) = do tag 13; toBuf b fc
    toBuf b (CCrash fc msg) = do tag 14; toBuf b fc; toBuf b msg

    fromBuf b
        = assert_total $ case !getTag of
               0 => do fc <- fromBuf b
                       idx <- fromBuf b
                       let Just x = getName idx vars
                           | Nothing => corrupt "CExp"
                       pure (CLocal {x} fc (mkPrf idx))
               1 => do fc <- fromBuf b
                       n <- fromBuf b
                       pure (CRef fc n)
               2 => do fc <- fromBuf b
                       x <- fromBuf b; sc <- fromBuf b
                       pure (CLam fc x sc)
               3 => do fc <- fromBuf b
                       x <- fromBuf b; inl <- fromBuf b; val <- fromBuf b; sc <- fromBuf b
                       pure (CLet fc x inl val sc)
               4 => do fc <- fromBuf b
                       f <- fromBuf b; as <- fromBuf b
                       pure (CApp fc f as)
               5 => do fc <- fromBuf b
                       t <- fromBuf b; n <- fromBuf b; as <- fromBuf b
                       pure (CCon fc t n as)
               6 => do fc <- fromBuf b
                       arity <- fromBuf b; op <- fromBuf b; args <- fromBuf b
                       pure (COp {arity} fc op args)
               7 => do fc <- fromBuf b
                       p <- fromBuf b; as <- fromBuf b
                       pure (CExtPrim fc p as)
               8 => do fc <- fromBuf b
                       x <- fromBuf b
                       pure (CForce fc x)
               9 => do fc <- fromBuf b
                       x <- fromBuf b
                       pure (CDelay fc x)
               10 => do fc <- fromBuf b
                        sc <- fromBuf b; alts <- fromBuf b; def <- fromBuf b
                        pure (CConCase fc sc alts def)
               11 => do fc <- fromBuf b
                        sc <- fromBuf b; alts <- fromBuf b; def <- fromBuf b
                        pure (CConstCase fc sc alts def)
               12 => do fc <- fromBuf b
                        c <- fromBuf b
                        pure (CPrimVal fc c)
               13 => do fc <- fromBuf b
                        pure (CErased fc)
               14 => do fc <- fromBuf b
                        msg <- fromBuf b
                        pure (CCrash fc msg)
               _ => corrupt "CExp"

  export
  {vars : _} -> TTC (CConAlt vars) where
    toBuf b (MkConAlt n t as sc) = do toBuf b n; toBuf b t; toBuf b as; toBuf b sc

    fromBuf b
        = do n <- fromBuf b; t <- fromBuf b
             as <- fromBuf b; sc <- fromBuf b
             pure (MkConAlt n t as sc)

  export
  {vars : _} -> TTC (CConstAlt vars) where
    toBuf b (MkConstAlt c sc) = do toBuf b c; toBuf b sc

    fromBuf b
        = do c <- fromBuf b; sc <- fromBuf b
             pure (MkConstAlt c sc)

export
TTC CFType where
  toBuf b CFUnit = tag 0
  toBuf b CFInt = tag 1
  toBuf b CFUnsigned8 = tag 2
  toBuf b CFUnsigned16 = tag 3
  toBuf b CFUnsigned32 = tag 4
  toBuf b CFUnsigned64 = tag 5
  toBuf b CFString = tag 6
  toBuf b CFDouble = tag 7
  toBuf b CFChar = tag 8
  toBuf b CFPtr = tag 9
  toBuf b CFWorld = tag 10
  toBuf b (CFFun s t) = do tag 11; toBuf b s; toBuf b t
  toBuf b (CFIORes t) = do tag 12; toBuf b t
  toBuf b (CFStruct n a) = do tag 13; toBuf b n; toBuf b a
  toBuf b (CFUser n a) = do tag 14; toBuf b n; toBuf b a
  toBuf b CFGCPtr = tag 15
  toBuf b CFBuffer = tag 16

  fromBuf b
      = case !getTag of
             0 => pure CFUnit
             1 => pure CFInt
             2 => pure CFUnsigned8
             3 => pure CFUnsigned16
             4 => pure CFUnsigned32
             5 => pure CFUnsigned64
             6 => pure CFString
             7 => pure CFDouble
             8 => pure CFChar
             9 => pure CFPtr
             10 => pure CFWorld
             11 => do s <- fromBuf b; t <- fromBuf b; pure (CFFun s t)
             12 => do t <- fromBuf b; pure (CFIORes t)
             13 => do n <- fromBuf b; a <- fromBuf b; pure (CFStruct n a)
             14 => do n <- fromBuf b; a <- fromBuf b; pure (CFUser n a)
             15 => pure CFGCPtr
             16 => pure CFBuffer
             _ => corrupt "CFType"

export
TTC CDef where
  toBuf b (MkFun args cexpr) = do tag 0; toBuf b args; toBuf b cexpr
  toBuf b (MkCon t arity pos) = do tag 1; toBuf b t; toBuf b arity; toBuf b pos
  toBuf b (MkForeign cs args ret) = do tag 2; toBuf b cs; toBuf b args; toBuf b ret
  toBuf b (MkError cexpr) = do tag 3; toBuf b cexpr

  fromBuf b
      = case !getTag of
             0 => do args <- fromBuf b; cexpr <- fromBuf b
                     pure (MkFun args cexpr)
             1 => do t <- fromBuf b; arity <- fromBuf b; pos <- fromBuf b
                     pure (MkCon t arity pos)
             2 => do cs <- fromBuf b; args <- fromBuf b; ret <- fromBuf b
                     pure (MkForeign cs args ret)
             3 => do cexpr <- fromBuf b
                     pure (MkError cexpr)
             _ => corrupt "CDef"

export
TTC CG where
  toBuf b Chez = tag 0
  toBuf b Racket = tag 2
  toBuf b Gambit = tag 3
  toBuf b (Other s) = do tag 4; toBuf b s
  toBuf b Node = tag 5
  toBuf b Javascript = tag 6
  toBuf b RefC = tag 7

  fromBuf b
      = case !getTag of
             0 => pure Chez
             2 => pure Racket
             3 => pure Gambit
             4 => do s <- fromBuf b
                     pure (Other s)
             5 => pure Node
             6 => pure Javascript
             7 => pure RefC
             _ => corrupt "CG"

export
TTC PairNames where
  toBuf b l
      = do toBuf b (pairType l)
           toBuf b (fstName l)
           toBuf b (sndName l)
  fromBuf b
      = do ty <- fromBuf b
           d <- fromBuf b
           f <- fromBuf b
           pure (MkPairNs ty d f)

export
TTC RewriteNames where
  toBuf b l
      = do toBuf b (equalType l)
           toBuf b (rewriteName l)
  fromBuf b
      = do ty <- fromBuf b
           l <- fromBuf b
           pure (MkRewriteNs ty l)

export
TTC PrimNames where
  toBuf b l
      = do toBuf b (fromIntegerName l)
           toBuf b (fromStringName l)
           toBuf b (fromCharName l)
  fromBuf b
      = do i <- fromBuf b
           str <- fromBuf b
           c <- fromBuf b
           pure (MkPrimNs i str c)

export
TTC HoleInfo where
  toBuf b NotHole = tag 0
  toBuf b (SolvedHole n) = do tag 1; toBuf b n

  fromBuf b
      = case !getTag of
             0 => pure NotHole
             1 => do n <- fromBuf b; pure (SolvedHole n)
             _ => corrupt "HoleInfo"

export
TTC PMDefInfo where
  toBuf b l
      = do toBuf b (holeInfo l)
           toBuf b (alwaysReduce l)
  fromBuf b
      = do h <- fromBuf b
           r <- fromBuf b
           pure (MkPMDefInfo h r)

export
TTC TypeFlags where
  toBuf b l
      = do toBuf b (uniqueAuto l)
           toBuf b (external l)
  fromBuf b
      = do u <- fromBuf b
           e <- fromBuf b
           pure (MkTypeFlags u e)

export
TTC Def where
  toBuf b None = tag 0
  toBuf b (PMDef pi args ct rt pats)
      = do tag 1; toBuf b pi; toBuf b args; toBuf b ct; toBuf b pats
  toBuf b (ExternDef a)
      = do tag 2; toBuf b a
  toBuf b (ForeignDef a cs)
      = do tag 3; toBuf b a; toBuf b cs
  toBuf b (Builtin a)
      = throw (InternalError "Trying to serialise a Builtin")
  toBuf b (DCon t arity nt) = do tag 4; toBuf b t; toBuf b arity; toBuf b nt
  toBuf b (TCon t arity parampos detpos u ms datacons dets)
      = do tag 5; toBuf b t; toBuf b arity; toBuf b parampos
           toBuf b detpos; toBuf b u; toBuf b ms; toBuf b datacons
           toBuf b dets
  toBuf b (Hole locs p)
      = do tag 6; toBuf b locs; toBuf b (implbind p)
  toBuf b (BySearch c depth def)
      = do tag 7; toBuf b c; toBuf b depth; toBuf b def
  toBuf b (Guess guess envb constraints)
      = do tag 8; toBuf b guess; toBuf b envb; toBuf b constraints
  toBuf b ImpBind = tag 9
  toBuf b Delayed = tag 10

  fromBuf b
      = case !getTag of
             0 => pure None
             1 => do pi <- fromBuf b
                     args <- fromBuf b
                     ct <- fromBuf b
                     pats <- fromBuf b
                     pure (PMDef pi args ct (Unmatched "") pats)
             2 => do a <- fromBuf b
                     pure (ExternDef a)
             3 => do a <- fromBuf b
                     cs <- fromBuf b
                     pure (ForeignDef a cs)
             4 => do t <- fromBuf b; a <- fromBuf b; nt <- fromBuf b
                     pure (DCon t a nt)
             5 => do t <- fromBuf b; a <- fromBuf b
                     ps <- fromBuf b; dets <- fromBuf b;
                     u <- fromBuf b
                     ms <- fromBuf b; cs <- fromBuf b
                     detags <- fromBuf b
                     pure (TCon t a ps dets u ms cs detags)
             6 => do l <- fromBuf b
                     p <- fromBuf b
                     pure (Hole l (holeInit p))
             7 => do c <- fromBuf b; depth <- fromBuf b
                     def <- fromBuf b
                     pure (BySearch c depth def)
             8 => do g <- fromBuf b; envb <- fromBuf b; cs <- fromBuf b
                     pure (Guess g envb cs)
             9 => pure ImpBind
             10 => pure Context.Delayed
             _ => corrupt "Def"

export
TTC TotalReq where
  toBuf b Total = tag 0
  toBuf b CoveringOnly = tag 1
  toBuf b PartialOK = tag 2

  fromBuf b
      = case !getTag of
             0 => pure Total
             1 => pure CoveringOnly
             2 => pure PartialOK
             _ => corrupt "TotalReq"

TTC DefFlag where
  toBuf b Inline = tag 2
  toBuf b Invertible = tag 3
  toBuf b Overloadable = tag 4
  toBuf b TCInline = tag 5
  toBuf b (SetTotal x) = do tag 6; toBuf b x
  toBuf b BlockedHint = tag 7
  toBuf b Macro = tag 8
  toBuf b (PartialEval x) = tag 9 -- names not useful any more
  toBuf b AllGuarded = tag 10

  fromBuf b
      = case !getTag of
             2 => pure Inline
             3 => pure Invertible
             4 => pure Overloadable
             5 => pure TCInline
             6 => do x <- fromBuf b; pure (SetTotal x)
             7 => pure BlockedHint
             8 => pure Macro
             9 => pure (PartialEval [])
             10 => pure AllGuarded
             _ => corrupt "DefFlag"

export
TTC SizeChange where
  toBuf b Smaller = tag 0
  toBuf b Same = tag 1
  toBuf b Unknown = tag 2

  fromBuf b
      = case !getTag of
             0 => pure Smaller
             1 => pure Same
             2 => pure Unknown
             _ => corrupt "SizeChange"

export
TTC SCCall where
  toBuf b c = do toBuf b (fnCall c); toBuf b (fnArgs c)
  fromBuf b
      = do fn <- fromBuf b
           args <- fromBuf b
           pure (MkSCCall fn args)

export
TTC GlobalDef where
  toBuf b gdef
      = -- Only write full details for user specified names. The others will
        -- be holes where all we will ever need after loading is the definition
        do toBuf b (compexpr gdef)
           toBuf b (map toList (refersToRuntimeM gdef))
           toBuf b (location gdef)
           -- We don't need any of the rest for code generation, so if
           -- we're decoding then, we can skip these (see Compiler.Common
           -- for how it's decoded minimally there)
           toBuf b (multiplicity gdef)
           toBuf b (fullname gdef)
           toBuf b (map toList (refersToM gdef))
           toBuf b (definition gdef)
           when (isUserName (fullname gdef) || cwName (fullname gdef)) $
              do toBuf b (type gdef)
                 toBuf b (eraseArgs gdef)
                 toBuf b (safeErase gdef)
                 toBuf b (specArgs gdef)
                 toBuf b (inferrable gdef)
                 toBuf b (vars gdef)
                 toBuf b (visibility gdef)
                 toBuf b (totality gdef)
                 toBuf b (flags gdef)
                 toBuf b (invertible gdef)
                 toBuf b (noCycles gdef)
                 toBuf b (sizeChange gdef)
    where
      cwName : Name -> Bool
      cwName (CaseBlock _ _) = True
      cwName (WithBlock _ _) = True
      cwName _ = False
  fromBuf b
      = do cdef <- fromBuf b
           refsRList <- fromBuf b
           let refsR = map fromList refsRList
           loc <- fromBuf b
           mul <- fromBuf b
           name <- fromBuf b
           refsList <- fromBuf b
           let refs = map fromList refsList
           def <- fromBuf b
           if isUserName name
              then do ty <- fromBuf b
                      eargs <- fromBuf b;
                      seargs <- fromBuf b; specargs <- fromBuf b
                      iargs <- fromBuf b;
                      vars <- fromBuf b
                      vis <- fromBuf b; tot <- fromBuf b
                      fl <- fromBuf b
                      inv <- fromBuf b
                      c <- fromBuf b
                      sc <- fromBuf b
                      pure (MkGlobalDef loc name ty eargs seargs specargs iargs
                                        mul vars vis
                                        tot fl refs refsR inv c True def cdef Nothing sc)
              else pure (MkGlobalDef loc name (Erased loc False) [] [] [] []
                                     mul [] Public unchecked [] refs refsR
                                     False False True def cdef Nothing [])

export
TTC Transform where
  toBuf b (MkTransform {vars} n env lhs rhs)
      = do toBuf b vars
           toBuf b n
           toBuf b env
           toBuf b lhs
           toBuf b rhs

  fromBuf b
      = do vars <- fromBuf b
           n <- fromBuf b
           env <- fromBuf b
           lhs <- fromBuf b
           rhs <- fromBuf b
           pure (MkTransform {vars} n env lhs rhs)

-- decode : Context -> Int -> (update : Bool) -> ContextEntry -> Core GlobalDef
Core.Context.decode gam idx update (Coded bin)
    = do b <- newRef Bin bin
         def <- fromBuf b
         let a = getContent gam
         arr <- get Arr
         def' <- resolved gam def
         when update $ coreLift $ writeArray arr idx (Decoded def')
         pure def'
Core.Context.decode gam idx update (Decoded def) = pure def
