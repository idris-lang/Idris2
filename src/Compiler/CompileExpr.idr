module Compiler.CompileExpr

import Core.CaseTree
import public Core.CompileExpr
import Core.Context
import Core.Env
import Core.Name
import Core.Normalise
import Core.TT
import Core.Value

import Data.List
import Data.Maybe
import Libraries.Data.NameMap
import Data.Vect

%default covering

data Args
    = NewTypeBy Nat Nat
    | EraseArgs Nat (List Nat)
    | Arity Nat

||| Extract the number of arguments from a term, or return that it's
||| a newtype by a given argument position
numArgs : Defs -> Term vars -> Core Args
numArgs defs (Ref _ (TyCon tag arity) n) = pure (Arity arity)
numArgs defs (Ref _ _ n)
    = do Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure (Arity 0)
         case definition gdef of
           DCon _ arity Nothing => pure (EraseArgs arity (eraseArgs gdef))
           DCon _ arity (Just (_, pos)) => pure (NewTypeBy arity pos)
           PMDef _ args _ _ _ => pure (Arity (length args))
           ExternDef arity => pure (Arity arity)
           ForeignDef arity _ => pure (Arity arity)
           Builtin {arity} f => pure (Arity arity)
           _ => pure (Arity 0)
numArgs _ tm = pure (Arity 0)

weakenVar : Var ns -> Var (a :: ns)
weakenVar (MkVar p) = (MkVar (Later p))

etaExpand : {vars : _} ->
            Int -> Nat -> CExp vars -> List (Var vars) -> CExp vars
etaExpand i Z exp args = mkApp exp (map (mkLocal (getFC exp)) (reverse args))
  where
    mkLocal : FC -> (Var vars) -> CExp vars
    mkLocal fc (MkVar p) = CLocal fc p

    mkApp : CExp vars -> List (CExp vars) -> CExp vars
    mkApp tm [] = tm
    mkApp (CApp fc f args) args' = CApp fc f (args ++ args')
    mkApp (CCon fc n t args) args' = CCon fc n t (args ++ args')
    mkApp (CExtPrim fc p args) args' = CExtPrim fc p (args ++ args')
    mkApp tm args = CApp (getFC tm) tm args
etaExpand i (S k) exp args
    = CLam (getFC exp) (MN "eta" i)
             (etaExpand (i + 1) k (weaken exp)
                  (MkVar First :: map weakenVar args))

export
expandToArity : {vars : _} ->
                Nat -> CExp vars -> List (CExp vars) -> CExp vars
-- No point in applying to anything
expandToArity _ (CErased fc) _ = CErased fc
-- Overapplied; apply everything as single arguments
expandToArity Z f args = applyAll f args
  where
    applyAll : CExp vars -> List (CExp vars) -> CExp vars
    applyAll fn [] = fn
    applyAll fn (a :: args) = applyAll (CApp (getFC fn) fn [a]) args
expandToArity (S k) f (a :: args) = expandToArity k (addArg f a) args
  where
    addArg : CExp vars -> CExp vars -> CExp vars
    addArg (CApp fc fn args) a = CApp fc fn (args ++ [a])
    addArg (CCon fc n tag args) a = CCon fc n tag (args ++ [a])
    addArg (CExtPrim fc p args) a = CExtPrim fc p (args ++ [a])
    addArg f a = CApp (getFC f) f [a]
-- Underapplied, saturate with lambdas
expandToArity num fn [] = etaExpand 0 num fn []

applyNewType : {vars : _} ->
               Nat -> Nat -> CExp vars -> List (CExp vars) -> CExp vars
applyNewType arity pos fn args
    = let fn' = expandToArity arity fn args in
          keepArg fn' -- fn' might be lambdas, after eta expansion
  where
    keep : Nat -> List (CExp vs) -> CExp vs
    keep i [] = CErased (getFC fn) -- can't happen if all is well!
    keep i (x :: xs)
        = if i == pos
             then x
             else keep (1 + i) xs

    keepArg : CExp vs -> CExp vs
    keepArg (CLam fc x sc) = CLam fc x (keepArg sc)
    keepArg (CCon fc _ _ args) = keep 0 args
    keepArg tm = CErased (getFC fn)

dropPos : List Nat -> CExp vs -> CExp vs
dropPos epos (CLam fc x sc) = CLam fc x (dropPos epos sc)
dropPos epos (CCon fc c a args) = CCon fc c a (drop 0 args)
  where
    drop : Nat -> List (CExp vs) -> List (CExp vs)
    drop i [] = []
    drop i (x :: xs)
        = if i `elem` epos
             then drop (1 + i) xs
             else x :: drop (1 + i) xs
dropPos epos tm = tm

eraseConArgs : {vars : _} ->
               Nat -> List Nat -> CExp vars -> List (CExp vars) -> CExp vars
eraseConArgs arity epos fn args
    = let fn' = expandToArity arity fn args in
          dropPos epos fn' -- fn' might be lambdas, after eta expansion

mkDropSubst : Nat -> List Nat ->
              (rest : List Name) ->
              (vars : List Name) ->
              (vars' ** SubVars (vars' ++ rest) (vars ++ rest))
mkDropSubst i es rest [] = ([] ** SubRefl)
mkDropSubst i es rest (x :: xs)
    = let (vs ** sub) = mkDropSubst (1 + i) es rest xs in
          if i `elem` es
             then (vs ** DropCons sub)
             else (x :: vs ** KeepCons sub)

-- Rewrite applications of Nat-like constructors and functions to more optimal
-- versions using Integer

-- None of these should be hard coded, but we'll do it this way until we
-- have a more general approach to optimising data types!
-- NOTE: Make sure that names mentioned here are listed in 'natHackNames' in
-- Common.idr, so that they get compiled, as they won't be spotted by the
-- usual calls to 'getRefs'.
data Magic : Type where
  MagicCCon : Name -> (arity : Nat) -> -- checks
              (FC -> forall vars. Vect arity (CExp vars) -> CExp vars) -> -- translation
              Magic
  MagicCRef : Name -> (arity : Nat) -> -- checks
              (FC -> FC -> forall vars. Vect arity (CExp vars) -> CExp vars) -> --translation
              Magic

magic : List Magic -> CExp vars -> CExp vars
magic ms (CLam fc x exp) = CLam fc x (magic ms exp)
magic ms e = go ms e where

  fire : Magic -> CExp vars -> Maybe (CExp vars)
  fire (MagicCCon n arity f) (CCon fc n' _ es)
    = do guard (n == n')
         map (f fc) (toVect arity es)
  fire (MagicCRef n arity f) (CApp fc (CRef fc' n') es)
    = do guard (n == n')
         map (f fc fc') (toVect arity es)
  fire _ _ = Nothing

  go : List Magic -> CExp vars -> CExp vars
  go [] e = e
  go (m :: ms) e = case fire m e of
    Nothing => go ms e
    Just e' => e'

natMinus : FC -> FC -> forall vars. Vect 2 (CExp vars) -> CExp vars
natMinus fc fc' [m,n] = CApp fc (CRef fc' (UN "prim__sub_Integer")) [m, n]

-- TODO: next release remove this and use %builtin pragma
natHack : List Magic
natHack =
    [ MagicCRef (NS typesNS (UN "natToInteger")) 1
         (\ _, _, [k] => k)
    , MagicCRef (NS typesNS (UN "integerToNat")) 1
         (\ fc, fc', [k] => CApp fc (CRef fc' (NS typesNS (UN "prim__integerToNat"))) [k])
    , MagicCRef (NS typesNS (UN "plus")) 2
         (\ fc, fc', [m,n] => CApp fc (CRef fc' (UN "prim__add_Integer")) [m, n])
    , MagicCRef (NS typesNS (UN "mult")) 2
         (\ fc, fc', [m,n] => CApp fc (CRef fc' (UN "prim__mul_Integer")) [m, n])
    , MagicCRef (NS natNS (UN "minus")) 2 natMinus
    ]

-- get all transformation from %builtin pragmas
builtinMagic : Ref Ctxt Defs => Core (forall vars. CExp vars -> CExp vars)
builtinMagic = do
    defs <- get Ctxt
    let b = defs.builtinTransforms
    let nats = concatMap builtinMagicNat $ values $ natTyNames b
    pure $ magic $ natHack ++ nats
  where
    builtinMagicNat : NatBuiltin -> List Magic
    builtinMagicNat cons =
        [ MagicCCon cons.zero 0
             (\ fc, [] => CPrimVal fc (BI 0))
        , MagicCCon cons.succ 1
             (\ fc, [k] => CApp fc (CRef fc (UN "prim__add_Integer")) [CPrimVal fc (BI 1), k])
        ] -- TODO: add builtin pragmas for Nat related functions (to/from Integer, add, mult, minus, compare)

isNatCon : (zeroMap : NameMap ZERO) ->
           (succMap : NameMap SUCC) ->
           Name -> Bool
isNatCon zs ss n = isJust (lookup n zs) || isJust (lookup n ss)

natBranch : (zeroMap : NameMap ZERO) ->
           (succMap : NameMap SUCC) ->
           CConAlt vars -> Bool
natBranch zs ss (MkConAlt n _ _ _) = isNatCon zs ss n

trySBranch :
    (succMap : NameMap SUCC) ->
    CExp vars ->
    CConAlt vars ->
    Maybe (CExp vars)
trySBranch ss n (MkConAlt nm _ [arg] sc)
  = do guard $ isJust $ lookup nm ss
       let fc = getFC n
       pure (CLet fc arg True (natMinus fc fc [n, CPrimVal fc (BI 1)]) sc)
trySBranch _ _ _ = Nothing

tryZBranch :
    (zeroMap : NameMap ZERO) ->
    CConAlt vars ->
    Maybe (CExp vars)
tryZBranch zs (MkConAlt n _ [] sc)
   = do guard $ isJust $ lookup n zs
        pure sc
tryZBranch _ _ = Nothing

getSBranch :
    (succMap : NameMap SUCC) ->
    CExp vars ->
    List (CConAlt vars) ->
    Maybe (CExp vars)
getSBranch ss n [] = Nothing
getSBranch ss n (x :: xs) = trySBranch ss n x <+> getSBranch ss n xs

getZBranch :
    (zeroMap : NameMap ZERO) ->
    List (CConAlt vars) ->
    Maybe (CExp vars)
getZBranch zs [] = Nothing
getZBranch zs (x :: xs) = tryZBranch zs x <+> getZBranch zs xs

-- Rewrite case trees on Nat to be case trees on Integer
builtinNatTree' : (zeroMap : NameMap ZERO) ->
                  (succMap : NameMap SUCC) ->
                  CExp vars -> CExp vars
builtinNatTree' zs ss (CConCase fc sc alts def)
   = if any (natBranch zs ss) alts
        then let defb = maybe (CCrash fc "Nat case not covered") id def
                 scase = maybe defb id (getSBranch ss sc alts)
                 zcase = maybe defb id (getZBranch zs alts) in
                 CConstCase fc sc [MkConstAlt (BI 0) zcase] (Just scase)
        else CConCase fc sc alts def
builtinNatTree' zs ss t = t

builtinNatTree : Ref Ctxt Defs => Core (CExp vars -> CExp vars)
builtinNatTree = do
    defs <- get Ctxt
    let b = defs.builtinTransforms
    pure $ builtinNatTree' b.natZNames b.natSNames

-- Rewrite case trees on Bool/Ord to be case trees on Integer
-- TODO: Generalise to all finite enumerations
isFiniteEnum : Name -> Bool
isFiniteEnum (NS ns (UN n))
   =  ((n == "True" || n == "False") && ns == basicsNS) -- booleans
   || ((n == "LT" || n == "EQ" || n == "GT") && ns == eqOrdNS) -- comparison
isFiniteEnum _ = False

boolHackTree : CExp vars -> CExp vars
boolHackTree (CConCase fc sc alts def)
   = let x = traverse toBool alts
         Just alts' = x
              | Nothing => CConCase fc sc alts def in
         CConstCase fc sc alts' def
  where
    toBool : CConAlt vars -> Maybe (CConstAlt vars)
    toBool (MkConAlt nm (Just tag) [] sc)
        = do guard (isFiniteEnum nm)
             pure $ MkConstAlt (I tag) sc
    toBool _ = Nothing
boolHackTree t = t

mutual
  toCExpTm : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             (magic : forall vars. CExp vars -> CExp vars) ->
             Name -> Term vars ->
             Core (CExp vars)
  toCExpTm m n (Local fc _ _ prf)
      = pure $ CLocal fc prf
  -- TMP HACK: extend this to all types which look like enumerations after erasure
  toCExpTm m n (Ref fc (DataCon tag arity) fn)
      = if arity == Z && isFiniteEnum fn
        then pure $ CPrimVal fc (I tag)
        else -- get full name for readability, and %builtin Natural
             pure $ CCon fc !(getFullName fn) (Just tag) []
  toCExpTm m n (Ref fc (TyCon tag arity) fn)
      = pure $ CCon fc fn Nothing []
  toCExpTm m n (Ref fc _ fn)
      = do full <- getFullName fn
               -- ^ For readability of output code, and the Nat hack,
           pure $ CApp fc (CRef fc full) []
  toCExpTm m n (Meta fc mn i args)
      = pure $ CApp fc (CRef fc mn) !(traverse (toCExp m n) args)
  toCExpTm m n (Bind fc x (Lam _ _ _ _) sc)
      = pure $ CLam fc x !(toCExp m n sc)
  toCExpTm m n (Bind fc x (Let _ rig val _) sc)
      = do sc' <- toCExp m n sc
           pure $ branchZero (shrinkCExp (DropCons SubRefl) sc')
                          (CLet fc x True !(toCExp m n val) sc')
                          rig
  toCExpTm m n (Bind fc x (Pi _ c e ty) sc)
      = pure $ CCon fc (UN "->") Nothing [!(toCExp m n ty),
                                    CLam fc x !(toCExp m n sc)]
  toCExpTm m n (Bind fc x b tm) = pure $ CErased fc
  -- We'd expect this to have been dealt with in toCExp, but for completeness...
  toCExpTm m n (App fc tm arg)
      = pure $ CApp fc !(toCExp m n tm) [!(toCExp m n arg)]
  -- This shouldn't be in terms any more, but here for completeness
  toCExpTm m n (As _ _ _ p) = toCExpTm m n p
  -- TODO: Either make sure 'Delayed' is always Rig0, or add to typecase
  toCExpTm m n (TDelayed fc _ _) = pure $ CErased fc
  toCExpTm m n (TDelay fc lr _ arg)
      = pure (CDelay fc lr !(toCExp m n arg))
  toCExpTm m n (TForce fc lr arg)
      = pure (CForce fc lr !(toCExp m n arg))
  toCExpTm m n (PrimVal fc c)
      = let t = constTag c in
            if t == 0
               then pure $ CPrimVal fc c
               else pure $ CCon fc (UN (show c)) Nothing []
  toCExpTm m n (Erased fc _) = pure $ CErased fc
  toCExpTm m n (TType fc) = pure $ CCon fc (UN "Type") Nothing []

  toCExp : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           (magic : forall vars. CExp vars -> CExp vars) ->
           Name -> Term vars ->
           Core (CExp vars)
  toCExp m n tm
      = case getFnArgs tm of
             (f, args) =>
                do args' <- traverse (toCExp m n) args
                   defs <- get Ctxt
                   f' <- toCExpTm m n f
                   Arity a <- numArgs defs f
                      | NewTypeBy arity pos =>
                            do let res = applyNewType arity pos f' args'
                               pure $ m res
                      | EraseArgs arity epos =>
                            do let res = eraseConArgs arity epos f' args'
                               pure $ m res
                   let res = expandToArity a f' args'
                   pure $ m res

mutual
  conCases : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             Name -> List (CaseAlt vars) ->
             Core (List (CConAlt vars))
  conCases n [] = pure []
  conCases {vars} n (ConCase x tag args sc :: ns)
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact x (gamma defs)
                | Nothing => -- primitive type match
                     do xn <- getFullName x
                        pure $ MkConAlt xn Nothing args !(toCExpTree n sc)
                                  :: !(conCases n ns)
           case (definition gdef) of
                DCon _ arity (Just pos) => conCases n ns -- skip it
                _ => do xn <- getFullName x
                        let (args' ** sub)
                            = mkDropSubst 0 (eraseArgs gdef) vars args
                        sc' <- toCExpTree n sc
                        ns' <- conCases n ns
                        if dcon (definition gdef)
                           then pure $ MkConAlt xn (Just tag) args' (shrinkCExp sub sc') :: ns'
                           else pure $ MkConAlt xn Nothing args' (shrinkCExp sub sc') :: ns'
    where
      dcon : Def -> Bool
      dcon (DCon _ _ _) = True
      dcon _ = False
  conCases n (_ :: ns) = conCases n ns

  constCases : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               Name -> List (CaseAlt vars) ->
               Core (List (CConstAlt vars))
  constCases n [] = pure []
  constCases n (ConstCase WorldVal sc :: ns)
      = constCases n ns
  constCases n (ConstCase x sc :: ns)
      = pure $ MkConstAlt x !(toCExpTree n sc) ::
                    !(constCases n ns)
  constCases n (_ :: ns) = constCases n ns

  -- If there's a case which matches on a 'newtype', return the RHS
  -- without matching.
  -- Take some care if the newtype involves a WorldVal - in that case we
  -- still need to let bind the scrutinee to ensure it's evaluated exactly
  -- once.
  getNewType : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               FC -> CExp vars ->
               Name -> List (CaseAlt vars) ->
               Core (Maybe (CExp vars))
  getNewType fc scr n [] = pure Nothing
  getNewType fc scr n (DefaultCase sc :: ns)
      = pure $ Nothing
  getNewType {vars} fc scr n (ConCase x tag args sc :: ns)
      = do defs <- get Ctxt
           case !(lookupDefExact x (gamma defs)) of
                -- If the flag is False, we still take the
                -- default, but need to evaluate the scrutinee of the
                -- case anyway - if the data structure contains a %World,
                -- that we've erased, it means it has interacted with the
                -- outside world, so we need to evaluate to keep the
                -- side effect.
                Just (DCon _ arity (Just (noworld, pos))) =>
-- FIXME: We don't need the commented out bit *for now* because io_bind
-- isn't being inlined, but it does need to be a little bit cleverer to
-- get the best performance.
-- I'm (edwinb) keeping it visible here because I plan to put it back in
-- more or less this form once case inlining works better and the whole thing
-- works in a nice principled way.
--                      if noworld -- just substitute the scrutinee into
--                                 -- the RHS
--                         then
                             let env : SubstCEnv args vars
                                     = mkSubst 0 scr pos args in
                                 pure $ Just (substs env !(toCExpTree n sc))
--                         else -- let bind the scrutinee, and substitute the
--                              -- name into the RHS
--                              let env : SubstCEnv args (MN "eff" 0 :: vars)
--                                      = mkSubst 0 (CLocal fc First) pos args in
--                              do sc' <- toCExpTree n sc
--                                 let scope = insertNames {outer=args}
--                                                         {inner=vars}
--                                                         [MN "eff" 0] sc'
--                                 pure $ Just (CLet fc (MN "eff" 0) False scr
--                                                   (substs env scope))
                _ => pure Nothing -- there's a normal match to do
    where
      mkSubst : Nat -> CExp vs ->
                Nat -> (args : List Name) -> SubstCEnv args vs
      mkSubst _ _ _ [] = Nil
      mkSubst i scr pos (a :: as)
          = if i == pos
               then scr :: mkSubst (1 + i) scr pos as
               else CErased fc :: mkSubst (1 + i) scr pos as
  getNewType fc scr n (_ :: ns) = getNewType fc scr n ns

  getDef : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           Name -> List (CaseAlt vars) ->
           Core (Maybe (CExp vars))
  getDef n [] = pure Nothing
  getDef n (DefaultCase sc :: ns)
      = pure $ Just !(toCExpTree n sc)
  getDef n (ConstCase WorldVal sc :: ns)
      = pure $ Just !(toCExpTree n sc)
  getDef n (_ :: ns) = getDef n ns

  toCExpTree : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               Name -> CaseTree vars ->
               Core (CExp vars)
  toCExpTree n alts@(Case _ x scTy (DelayCase ty arg sc :: rest))
      = let fc = getLoc scTy in
            pure $
              CLet fc arg True (CForce fc LInf (CLocal (getLoc scTy) x)) $
              CLet fc ty True (CErased fc)
                   !(toCExpTree n sc)
  toCExpTree n alts
      = toCExpTree' n alts

  toCExpTree' : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                Name -> CaseTree vars ->
                Core (CExp vars)
  toCExpTree' n (Case _ x scTy alts@(ConCase _ _ _ _ :: _))
      = let fc = getLoc scTy in
            do Nothing <- getNewType fc (CLocal fc x) n alts
                   | Just def => pure def
               defs <- get Ctxt
               cases <- conCases n alts
               def <- getDef n alts
               if isNil cases
                  then pure (fromMaybe (CErased fc) def)
                  else pure $ boolHackTree $ !builtinNatTree $
                            CConCase fc (CLocal fc x) cases def
  toCExpTree' n (Case _ x scTy alts@(DelayCase _ _ _ :: _))
      = throw (InternalError "Unexpected DelayCase")
  toCExpTree' n (Case fc x scTy alts@(ConstCase _ _ :: _))
      = let fc = getLoc scTy in
            do cases <- constCases n alts
               def <- getDef n alts
               if isNil cases
                  then pure (fromMaybe (CErased fc) def)
                  else pure $ CConstCase fc (CLocal fc x) cases def
  toCExpTree' n (Case _ x scTy alts@(DefaultCase sc :: _))
      = toCExpTree n sc
  toCExpTree' n (Case _ x scTy [])
      = pure $ CCrash (getLoc scTy) $ "Missing case tree in " ++ show n
  toCExpTree' n (STerm _ tm) = toCExp !builtinMagic n tm
  toCExpTree' n (Unmatched msg)
      = pure $ CCrash emptyFC msg
  toCExpTree' n Impossible
      = pure $ CCrash emptyFC ("Impossible case encountered in " ++ show n)

-- Need this for ensuring that argument list matches up to operator arity for
-- builtins
data ArgList : Nat -> List Name -> Type where
     NoArgs : ArgList Z []
     ConsArg : (a : Name) -> ArgList k as -> ArgList (S k) (a :: as)

mkArgList : Int -> (n : Nat) -> (ns ** ArgList n ns)
mkArgList i Z = (_ ** NoArgs)
mkArgList i (S k)
    = let (_ ** rec) = mkArgList (i + 1) k in
          (_ ** ConsArg (MN "arg" i) rec)

data NArgs : Type where
     User : Name -> List (Closure []) -> NArgs
     Struct : String -> List (String, Closure []) -> NArgs
     NUnit : NArgs
     NPtr : NArgs
     NGCPtr : NArgs
     NBuffer : NArgs
     NIORes : Closure [] -> NArgs

getPArgs : {auto c : Ref Ctxt Defs} ->
           Defs -> Closure [] -> Core (String, Closure [])
getPArgs defs cl
    = do NDCon fc _ _ _ args <- evalClosure defs cl
             | nf => throw (GenericMsg (getLoc nf) "Badly formed struct type")
         case reverse (map snd args) of
              (tydesc :: n :: _) =>
                  do NPrimVal _ (Str n') <- evalClosure defs n
                         | nf => throw (GenericMsg (getLoc nf) "Unknown field name")
                     pure (n', tydesc)
              _ => throw (GenericMsg fc "Badly formed struct type")

getFieldArgs : {auto c : Ref Ctxt Defs} ->
               Defs -> Closure [] -> Core (List (String, Closure []))
getFieldArgs defs cl
    = do NDCon fc _ _ _ args <- evalClosure defs cl
             | nf => throw (GenericMsg (getLoc nf) "Badly formed struct type")
         case map snd args of
              -- cons
              [_, t, rest] =>
                  do rest' <- getFieldArgs defs rest
                     (n, ty) <- getPArgs defs t
                     pure ((n, ty) :: rest')
              -- nil
              _ => pure []

getNArgs : {auto c : Ref Ctxt Defs} ->
           Defs -> Name -> List (Closure []) -> Core NArgs
getNArgs defs (NS _ (UN "IORes")) [arg] = pure $ NIORes arg
getNArgs defs (NS _ (UN "Ptr")) [arg] = pure NPtr
getNArgs defs (NS _ (UN "AnyPtr")) [] = pure NPtr
getNArgs defs (NS _ (UN "GCPtr")) [arg] = pure NGCPtr
getNArgs defs (NS _ (UN "GCAnyPtr")) [] = pure NGCPtr
getNArgs defs (NS _ (UN "Buffer")) [] = pure NBuffer
getNArgs defs (NS _ (UN "Unit")) [] = pure NUnit
getNArgs defs (NS _ (UN "Struct")) [n, args]
    = do NPrimVal _ (Str n') <- evalClosure defs n
             | nf => throw (GenericMsg (getLoc nf) "Unknown name for struct")
         pure (Struct n' !(getFieldArgs defs args))
getNArgs defs n args = pure $ User n args

nfToCFType : {auto c : Ref Ctxt Defs} ->
             FC -> (inStruct : Bool) -> NF [] -> Core CFType
nfToCFType _ _ (NPrimVal _ IntType) = pure CFInt
nfToCFType _ _ (NPrimVal _ Bits8Type) = pure CFUnsigned8
nfToCFType _ _ (NPrimVal _ Bits16Type) = pure CFUnsigned16
nfToCFType _ _ (NPrimVal _ Bits32Type) = pure CFUnsigned32
nfToCFType _ _ (NPrimVal _ Bits64Type) = pure CFUnsigned64
nfToCFType _ False (NPrimVal _ StringType) = pure CFString
nfToCFType fc True (NPrimVal _ StringType)
    = throw (GenericMsg fc "String not allowed in a foreign struct")
nfToCFType _ _ (NPrimVal _ DoubleType) = pure CFDouble
nfToCFType _ _ (NPrimVal _ CharType) = pure CFChar
nfToCFType _ _ (NPrimVal _ WorldType) = pure CFWorld
nfToCFType _ False (NBind fc _ (Pi _ _ _ ty) sc)
    = do defs <- get Ctxt
         sty <- nfToCFType fc False ty
         sc' <- sc defs (toClosure defaultOpts [] (Erased fc False))
         tty <- nfToCFType fc False sc'
         pure (CFFun sty tty)
nfToCFType _ True (NBind fc _ _ _)
    = throw (GenericMsg fc "Function types not allowed in a foreign struct")
nfToCFType _ s (NTCon fc n_in _ _ args)
    = do defs <- get Ctxt
         n <- toFullNames n_in
         case !(getNArgs defs n $ map snd args) of
              User un uargs =>
                do nargs <- traverse (evalClosure defs) uargs
                   cargs <- traverse (nfToCFType fc s) nargs
                   pure (CFUser n cargs)
              Struct n fs =>
                do fs' <- traverse
                             (\ (n, ty) =>
                                    do tynf <- evalClosure defs ty
                                       tycf <- nfToCFType fc True tynf
                                       pure (n, tycf)) fs
                   pure (CFStruct n fs')
              NUnit => pure CFUnit
              NPtr => pure CFPtr
              NGCPtr => pure CFGCPtr
              NBuffer => pure CFBuffer
              NIORes uarg =>
                do narg <- evalClosure defs uarg
                   carg <- nfToCFType fc s narg
                   pure (CFIORes carg)
nfToCFType _ s (NType _)
    = pure (CFUser (UN "Type") [])
nfToCFType _ s (NErased _ _)
    = pure (CFUser (UN "__") [])
nfToCFType fc s t
    = do defs <- get Ctxt
         ty <- quote defs [] t
         throw (GenericMsg (getLoc t)
                       ("Can't marshal type for foreign call " ++
                                      show !(toFullNames ty)))

getCFTypes : {auto c : Ref Ctxt Defs} ->
             List CFType -> NF [] ->
             Core (List CFType, CFType)
getCFTypes args (NBind fc _ (Pi _ _ _ ty) sc)
    = do aty <- nfToCFType fc False ty
         defs <- get Ctxt
         sc' <- sc defs (toClosure defaultOpts [] (Erased fc False))
         getCFTypes (aty :: args) sc'
getCFTypes args t
    = pure (reverse args, !(nfToCFType (getLoc t) False t))

toCDef : {auto c : Ref Ctxt Defs} ->
         Name -> ClosedTerm -> Def ->
         Core CDef
toCDef n ty None
    = pure $ MkError $ CCrash emptyFC ("Encountered undefined name " ++ show !(getFullName n))
toCDef n ty (PMDef _ args _ tree _)
    = pure $ MkFun _ !(toCExpTree n tree)
toCDef n ty (ExternDef arity)
    = let (ns ** args) = mkArgList 0 arity in
          pure $ MkFun _ (CExtPrim emptyFC !(getFullName n) (map toArgExp (getVars args)))
  where
    toArgExp : (Var ns) -> CExp ns
    toArgExp (MkVar p) = CLocal emptyFC p

    getVars : ArgList k ns -> List (Var ns)
    getVars NoArgs = []
    getVars (ConsArg a rest) = MkVar First :: map weakenVar (getVars rest)
toCDef n ty (ForeignDef arity cs)
    = do defs <- get Ctxt
         (atys, retty) <- getCFTypes [] !(nf defs [] ty)
         pure $ MkForeign cs atys retty
toCDef n ty (Builtin {arity} op)
    = let (ns ** args) = mkArgList 0 arity in
          pure $ MkFun _ (COp emptyFC op (map toArgExp (getVars args)))
  where
    toArgExp : (Var ns) -> CExp ns
    toArgExp (MkVar p) = CLocal emptyFC p

    getVars : ArgList k ns -> Vect k (Var ns)
    getVars NoArgs = []
    getVars (ConsArg a rest) = MkVar First :: map weakenVar (getVars rest)
toCDef n _ (DCon tag arity pos)
    = do let nt = snd <$> pos
         defs <- get Ctxt
         args <- numArgs {vars = []} defs (Ref EmptyFC (DataCon tag arity) n)
         let arity' = case args of
                 NewTypeBy ar _ => ar
                 EraseArgs ar erased => ar `minus` length erased
                 Arity ar => ar
         pure $ MkCon (Just tag) arity' nt
toCDef n _ (TCon tag arity _ _ _ _ _ _)
    = pure $ MkCon Nothing arity Nothing
-- We do want to be able to compile these, but also report an error at run time
-- (and, TODO: warn at compile time)
toCDef n ty (Hole _ _)
    = pure $ MkError $ CCrash emptyFC ("Encountered unimplemented hole " ++
                                       show !(getFullName n))
toCDef n ty (Guess _ _ _)
    = pure $ MkError $ CCrash emptyFC ("Encountered constrained hole " ++
                                       show !(getFullName n))
toCDef n ty (BySearch _ _ _)
    = pure $ MkError $ CCrash emptyFC ("Encountered incomplete proof search " ++
                                       show !(getFullName n))
toCDef n ty def
    = pure $ MkError $ CCrash emptyFC ("Encountered uncompilable name " ++
                                       show (!(getFullName n), def))

export
compileExp : {auto c : Ref Ctxt Defs} ->
             ClosedTerm -> Core (CExp [])
compileExp tm
    = do m <- builtinMagic
         exp <- toCExp m (UN "main") tm
         pure exp

||| Given a name, look up an expression, and compile it to a CExp in the environment
export
compileDef : {auto c : Ref Ctxt Defs} -> Name -> Core ()
compileDef n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (InternalError ("Trying to compile unknown name " ++ show n))
         ce <- toCDef n (type gdef)
                             !(toFullNames (definition gdef))
         setCompiled n ce

export
mkForgetDef : {auto c : Ref Ctxt Defs} ->
              Name -> Core ()
mkForgetDef n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (InternalError ("Trying to compile unknown name " ++ show n))
         case compexpr gdef of
              Nothing => pure ()
              Just cdef => do let ncdef = forgetDef cdef
                              setNamedCompiled n ncdef
