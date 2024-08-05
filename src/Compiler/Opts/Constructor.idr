{-
Optimisations which rewrite constructors and cases to more optimised versions.
In general optimisations here may change the representation of data types
so after making changes here you may need to update the ttc version

Nat hack - constructors with ZERO or SUCC ConInfo are replaced with 0 : Integer and (1 +) : Integer -> Integer respectively
         - cases on ZERO and SUCC are replaced with checking if the integer is 0

Enums - enums (ie data types where all constructors are nullary after erasure) are replaced with a finite integer (Bits8, Bits16 or Bits32)

Unit - case blocks scrutinising UNIT are removed (possibly leaving behind a non-inlinable let binding)

Intrinsic constructors: NIL/CONS, NOTHING/JUST - these are left as constructors,
    but the name and tag are based on the ConInfo rather than the original name and tag.
    new `CDef`s must be generated for each of these constructors - see intrinsicCons.
-}

module Compiler.Opts.Constructor

import Core.CompileExpr
import Core.Context
import Core.Name
import Core.TT
import Data.Vect

export
data NextMN : Type where

export
newMN : Ref NextMN Int => String -> Core Name
newMN base = do
    x <- get NextMN
    put NextMN $ x + 1
    pure $ MN base x


-- Rewrite applications of Nat-like constructors and functions to more optimal
-- versions using Integer

-- None of these should be hard coded, but we'll do it this way until we
-- have a more general approach to optimising data types!
-- NOTE: Make sure that names mentioned here are listed in 'natHackNames' in
-- Common.idr, so that they get compiled, as they won't be spotted by the
-- usual calls to 'getRefs'.
data Magic : Type where
    MagicCRef :
        Name -> (arity : Nat) -> -- checks
        (FC -> FC -> forall vars. Vect arity (CExp vars) -> CExp vars) -> --translation
        Magic

magic : List Magic -> CExp vars -> Maybe (CExp vars)
magic ms (CLam fc x exp) = CLam fc x <$> magic ms exp
magic ms e = go ms e where

    fire : Magic -> CExp vars -> Maybe (CExp vars)
    fire (MagicCRef n arity f) (CApp fc (CRef fc' n') es) = do
        guard (n == n')
        map (f fc fc') (toVect arity es)
    fire _ _ = Nothing

    go : List Magic -> CExp vars -> Maybe (CExp vars)
    go [] e = Nothing
    go (m :: ms) e = case fire m e of
        Nothing => go ms e
        Just e' => Just e'

magic__integerToNat : FC -> FC -> forall vars. Vect 1 (CExp vars) -> CExp vars
magic__integerToNat fc fc' [k]
  = CApp fc (CRef fc' (NS typesNS (UN $ Basic "prim__integerToNat"))) [k]

magic__natMinus : FC -> FC -> forall vars. Vect 2 (CExp vars) -> CExp vars
magic__natMinus fc fc' [m, n]
  = magic__integerToNat fc fc'
    [COp fc (Sub IntegerType) [m, n]]

-- We don't reuse natMinus here because we assume that unsuc will only be called
-- on S-headed numbers so we do not need the truncating integerToNat call!
magic__natUnsuc : FC -> FC -> forall vars. Vect 1 (CExp vars) -> CExp vars
magic__natUnsuc fc fc' [m]
  = COp fc (Sub IntegerType) [m, CPrimVal fc (BI 1)]

-- TODO: next release remove this and use %builtin pragma
natHack : List Magic
natHack =
    [ MagicCRef (NS typesNS (UN $ Basic "natToInteger")) 1 (\ _, _, [k] => k)
    , MagicCRef (NS typesNS (UN $ Basic "integerToNat")) 1 magic__integerToNat
    , MagicCRef (NS typesNS (UN $ Basic "plus")) 2
         (\ fc, fc', [m,n] => COp fc (Add IntegerType) [m, n])
    , MagicCRef (NS typesNS (UN $ Basic "mult")) 2
         (\ fc, fc', [m,n] => COp fc (Mul IntegerType) [m, n])
    , MagicCRef (NS typesNS (UN $ Basic "minus")) 2 magic__natMinus
    , MagicCRef (NS typesNS (UN $ Basic "equalNat")) 2
         (\ fc, fc', [m,n] => COp fc (EQ IntegerType) [m, n])
    , MagicCRef (NS typesNS (UN $ Basic "compareNat")) 2
         (\ fc, fc', [m,n] => CApp fc (CRef fc' (NS eqOrdNS (UN $ Basic "compareInteger"))) [m, n])
    ]

-- get all builtin transformations
builtinMagic : forall vars. CExp vars -> Maybe (CExp vars)
builtinMagic = magic natHack

natBranch :  CConAlt vars -> Bool
natBranch (MkConAlt n ZERO _ _ _) = True
natBranch (MkConAlt n SUCC _ _ _) = True
natBranch _ = False

trySBranch : CExp vars -> CConAlt vars -> Maybe (CExp vars)
trySBranch n (MkConAlt nm SUCC _ (arg :%: SLNil) sc)
    = Just (CLet (getFC n) arg YesInline (magic__natUnsuc (getFC n) (getFC n) [n]) sc)
trySBranch _ _ = Nothing

tryZBranch : CConAlt vars -> Maybe (CExp vars)
tryZBranch (MkConAlt n ZERO _ SLNil sc) = Just sc
tryZBranch _ = Nothing

getSBranch : CExp vars -> List (CConAlt vars) -> Maybe (CExp vars)
getSBranch n [] = Nothing
getSBranch n (x :: xs) = trySBranch n x <|> getSBranch n xs

getZBranch : List (CConAlt vars) -> Maybe (CExp vars)
getZBranch [] = Nothing
getZBranch (x :: xs) = tryZBranch x <|> getZBranch xs

-- Rewrite case trees on Nat to be case trees on Integer
nat : {auto s : Ref NextMN Int} -> CExp vars -> Core (Maybe (CExp vars))
nat (CCon fc _ ZERO _ []) = pure $ Just $ CPrimVal fc (BI 0)
nat (CCon fc _ SUCC _ [x]) = pure $ Just $ COp fc (Add IntegerType) [CPrimVal fc (BI 1), x]
nat (CConCase fc sc@(CLocal _ _) alts def) =
    pure $ if any natBranch alts
            then
                let defb = fromMaybe (CCrash fc "Nat case not covered") def
                    salt = maybe defb id (getSBranch sc alts)
                    zalt = maybe defb id (getZBranch alts)
                in Just (CConstCase fc sc [MkConstAlt (BI 0) zalt] (Just salt))
            else Nothing
nat (CConCase fc sc alts def) = do
    x <- newMN "succ"
    Just t <- nat (CConCase fc (CLocal fc First) (map weaken alts) (map weaken def))
        | Nothing => pure Nothing
    pure $ Just $ CLet fc x YesInline sc t
nat _ = pure Nothing

{-
=========
  Enums
=========
-}

enumTag : Nat -> Int -> Constant
enumTag k i =
  if      k <= 0xff   then B8 (cast i)
  else if k <= 0xffff then B16 (cast i)
  else                     B32 (cast i)

enum : CExp vars -> Maybe (CExp vars)
enum (CCon fc _ (ENUM n) (Just tag) []) = Just (CPrimVal fc (enumTag n tag))
enum (CConCase fc sc alts def) = do
    alts' <- traverse toEnum alts
    Just $ CConstCase fc sc alts' def
  where
    toEnum : CConAlt vars -> Maybe (CConstAlt vars)
    toEnum (MkConAlt nm (ENUM n) (Just tag) SLNil sc)
        = pure $ MkConstAlt (enumTag n tag) sc
    toEnum _ = Nothing
enum t = Nothing

{-
========
  Unit
========
-}

unitTree : Ref NextMN Int => CExp vars -> Core (Maybe (CExp vars))
unitTree exp@(CConCase fc sc alts def) =
    let [MkConAlt _ UNIT _ SLNil e] = alts
            | _ => pure Nothing
    in case sc of -- TODO: Check scrutinee has no effect, and skip let binding
        CLocal _ _ => pure $ Just e
        _ => pure $ Just $ CLet fc !(newMN "_unit") NotInline sc (weaken e)
unitTree t = pure Nothing

{-
==========================
  Intrinsic constructors
==========================
-}

mkIntrinsicName : String -> Name
mkIntrinsicName x = mkNamespacedName (Just intrinsicNS) (Basic x)
  where
    intrinsicNS : Namespace
    intrinsicNS = mkNamespace "_builtin"

conInfoNameTag : ConInfo -> Maybe (Name, Int)
conInfoNameTag NIL = Just (mkIntrinsicName "NIL", 0)
conInfoNameTag CONS = Just (mkIntrinsicName "CONS", 1)
conInfoNameTag NOTHING = Just (mkIntrinsicName "NOTHING", 0)
conInfoNameTag JUST = Just (mkIntrinsicName "JUST", 1)
conInfoNameTag _ = Nothing

export
intrinsicCons : List (Name, FC, CDef)
intrinsicCons = process
    [ (NIL, 0)
    , (CONS, 2)
    , (NOTHING, 0)
    , (JUST, 1)
    ]
  where
    process : List (ConInfo, Nat) -> List (Name, FC, CDef)
    process = mapMaybe $ \(ci, ar) =>
        map (\(n, tag) => (n, (EmptyFC, MkCon (Just tag) ar Nothing))) $ conInfoNameTag ci

tryIntrinsic : CExp vars -> Maybe (CExp vars)
tryIntrinsic (CCon fc _ ci _ xs) =
    conInfoNameTag ci <&> \(n, tag) => CCon fc n ci (Just tag) xs
tryIntrinsic (CConCase fc e alts def) =
    traverse go alts
        <&> \alts => CConCase fc e alts def
  where
    go : CConAlt vars -> Maybe (CConAlt vars)
    go (MkConAlt _ ci _ as e) =
        conInfoNameTag ci <&> \(n, tag) => MkConAlt n ci (Just tag) as e
tryIntrinsic _ = Nothing

parameters (try : forall vars. CExp vars -> Core (CExp vars))
    rewriteCExp : CExp vars -> Core (CExp vars)
    -- Recursively rewrite the sub-terms of a CExp
    rewriteSub : CExp vars -> Core (CExp vars)

    rewriteCConAlt : CConAlt vars -> Core (CConAlt vars)
    rewriteCConstAlt : CConstAlt vars -> Core (CConstAlt vars)

    rewriteCExp exp = do
        exp' <- try exp
        rewriteSub exp'

    rewriteSub (CLam fc x e) =
        CLam fc x <$> rewriteCExp e
    rewriteSub (CLet fc x inl e1 e2) =
        CLet fc x inl <$> rewriteCExp e1 <*> rewriteCExp e2
    rewriteSub (CApp fc f xs) =
        CApp fc <$> rewriteCExp f <*> traverse rewriteCExp xs
    rewriteSub (CCon fc n ci t xs) =
        CCon fc n ci t <$> traverse rewriteCExp xs
    rewriteSub (COp fc op xs) =
        COp fc op <$> traverseVect rewriteCExp xs
    rewriteSub (CExtPrim fc n xs) =
        CExtPrim fc n <$> traverse rewriteCExp xs
    rewriteSub (CForce fc lr e) =
        CForce fc lr <$> rewriteCExp e
    rewriteSub (CDelay fc lr e) =
        CDelay fc lr <$> rewriteCExp e
    rewriteSub (CConCase fc x alts def) =
        CConCase fc x <$> traverse rewriteCConAlt alts <*> traverseOpt rewriteCExp def
    rewriteSub (CConstCase fc x alts def) =
        CConstCase fc x <$> traverse rewriteCConstAlt alts <*> traverseOpt rewriteCExp def
    rewriteSub e = pure e

    rewriteCConAlt (MkConAlt n ci t as e) = MkConAlt n ci t as <$> rewriteCExp e
    rewriteCConstAlt (MkConstAlt x e) = MkConstAlt x <$> rewriteCExp e

sequence : List (forall vars. CExp vars -> Core (Maybe (CExp vars))) -> CExp vars -> Core (CExp vars)
sequence [] e = pure e
sequence (x :: xs) e = do
    e' <- fromMaybe e <$> x e
    sequence xs e'

export
constructorCExp : Ref NextMN Int => CExp vars -> Core (CExp vars)
constructorCExp = rewriteCExp rw
  where
    rw : forall vars. CExp vars -> Core (CExp vars)
    rw = sequence
        [ pure . builtinMagic
        , nat
        , pure . enum
        , unitTree
        , pure . tryIntrinsic
        ]


export
constructorCDef : Ref NextMN Int => CDef -> Core CDef
constructorCDef (MkFun args e) = MkFun args <$> constructorCExp e
constructorCDef def = pure def
