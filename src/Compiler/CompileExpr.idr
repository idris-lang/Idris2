module Compiler.CompileExpr

import Compiler.Opts.Constructor
import Core.Case.CaseTree
import public Core.CompileExpr
import Core.Context
import Core.Context.Log
import Core.Env
import Core.Name
import Core.Normalise
import Core.Options
import Core.TT
import Core.Value

import Data.List
import Data.SnocList
import Data.Maybe
import Data.Vect

import Libraries.Data.List.SizeOf
import Libraries.Data.SnocList.SizeOf
import Libraries.Data.SnocList.Extra

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
           PMDef _ args _ _ _ => pure (EraseArgs (length args) (eraseArgs gdef))
           ExternDef arity => pure (Arity arity)
           ForeignDef arity _ => pure (Arity arity)
           Builtin {arity} f => pure (Arity arity)
           _ => pure (Arity 0)
numArgs _ tm = pure (Arity 0)

mkSub : Nat -> (ns : Scope) -> List Nat -> (ns' ** Thin ns' ns)
mkSub i _ [] = (_ ** Refl)
mkSub i [] ns = (_ ** Refl)
mkSub i (x :: xs) es
    = let (ns' ** p) = mkSub (S i) xs es in
          if i `elem` es
             then (ns' ** Drop p)
             else (x :: ns' ** Keep p)

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
    mkApp (CCon fc n ci t args) args' = CCon fc n ci t (args ++ args')
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
    addArg (CCon fc n ci tag args) a = CCon fc n ci tag (args ++ [a])
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
    keepArg (CCon fc _ _ _ args) = keep 0 args
    keepArg tm = CErased (getFC fn)

dropFrom : List Nat -> Nat -> List (CExp vs) -> List (CExp vs)
dropFrom epos i [] = []
dropFrom epos i (x :: xs)
    = if i `elem` epos
         then dropFrom epos (1 + i) xs
         else x :: dropFrom epos (1 + i) xs

dropPos : List Nat -> CExp vs -> CExp vs
dropPos epos (CLam fc x sc) = CLam fc x (dropPos epos sc)
dropPos epos (CApp fc tm@(CApp _ _ _) args')
    = CApp fc (dropPos epos tm) args'
dropPos epos (CApp fc f args) = CApp fc f (dropFrom epos 0 args)
dropPos epos (CCon fc c ci a args) = CCon fc c ci a (dropFrom epos 0 args)
dropPos epos tm = tm

eraseConArgs : {vars : _} ->
               Nat -> List Nat -> CExp vars -> List (CExp vars) -> CExp vars
eraseConArgs arity epos fn args
    = let fn' = expandToArity arity fn args in
          if not (isNil epos)
             then dropPos epos fn' -- fn' might be lambdas, after eta expansion
             else fn'

mkDropSubst : Nat -> List Nat ->
              (rest : List Name) ->
              (vars : List Name) ->
              (vars' ** Thin (vars' ++ rest) (vars ++ rest))
mkDropSubst i es rest [] = ([] ** Refl)
mkDropSubst i es rest (x :: xs)
    = let (vs ** sub) = mkDropSubst (1 + i) es rest xs in
          if i `elem` es
             then (vs ** Drop sub)
             else (x :: vs ** Keep sub)

-- See if the constructor is a special constructor type, e.g a nil or cons
-- shaped thing.
dconFlag : {auto c : Ref Ctxt Defs} ->
           Name -> Core ConInfo
dconFlag n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (InternalError ("Can't find " ++ show n))
         pure (ciFlags (definition def) (flags def))
  where
    ciFlags : Def -> List DefFlag -> ConInfo
    ciFlags def [] = case def of
      TCon{} => TYCON
      _ => DATACON
    ciFlags def (ConType ci :: xs) = ci
    ciFlags def (x :: xs) = ciFlags def xs

toCExpTm : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           Name -> Term vars ->
           Core (CExp vars)
toCExp : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         Name -> Term vars ->
         Core (CExp vars)

toCExpTm n (Local fc _ _ prf)
    = pure $ CLocal fc prf
toCExpTm n (Ref fc (DataCon tag arity) fn)
    = do -- get full name for readability, and %builtin Natural
         cn <- getFullName fn
         fl <- dconFlag cn
         pure $ CCon fc cn fl (Just tag) []
toCExpTm n (Ref fc (TyCon tag arity) fn)
    = pure $ CCon fc fn TYCON Nothing []
toCExpTm n (Ref fc _ fn)
    = do full <- getFullName fn
             -- ^ For readability of output code, and the Nat hack,
         pure $ CApp fc (CRef fc full) []
toCExpTm n (Meta fc mn i args)
    = pure $ CApp fc (CRef fc mn) !(traverse (toCExp n) args)
toCExpTm n (Bind fc x (Lam _ _ _ _) sc)
    = pure $ CLam fc x !(toCExp n sc)
toCExpTm n (Bind fc x (Let _ rig val _) sc)
    = do sc' <- toCExp n sc
         pure $ branchZero (shrinkCExp (Drop Refl) sc')
                        (CLet fc x YesInline !(toCExp n val) sc')
                        rig
toCExpTm n (Bind fc x (Pi _ c e ty) sc)
    = pure $ CCon fc (UN (Basic "->")) TYCON Nothing
                     [ !(toCExp n ty)
                     , CLam fc x !(toCExp n sc)]
toCExpTm n (Bind fc x b tm) = pure $ CErased fc
-- We'd expect this to have been dealt with in toCExp, but for completeness...
toCExpTm n (App fc tm arg)
    = pure $ CApp fc !(toCExp n tm) [!(toCExp n arg)]
-- This shouldn't be in terms any more, but here for completeness
toCExpTm n (As _ _ _ p) = toCExpTm n p
-- TODO: Either make sure 'Delayed' is always Rig0, or add to typecase
toCExpTm n (TDelayed fc _ _) = pure $ CErased fc
toCExpTm n (TDelay fc lr _ arg)
    = pure (CDelay fc lr !(toCExp n arg))
toCExpTm n (TForce fc lr arg)
    = pure (CForce fc lr !(toCExp n arg))
toCExpTm n (PrimVal fc $ PrT c) = pure $ CCon fc (UN $ Basic $ show c) TYCON Nothing [] -- Primitive type constant
toCExpTm n (PrimVal fc c) = pure $ CPrimVal fc c -- Non-type constant
toCExpTm n (Erased fc _) = pure $ CErased fc
toCExpTm n (TType fc _) = pure $ CCon fc (UN (Basic "Type")) TYCON Nothing []

toCExp n tm
    = case getFnArgs tm of
           (f, args) =>
              do args' <- traverse (toCExp n) args
                 defs <- get Ctxt
                 f' <- toCExpTm n f
                 case !(numArgs defs f) of
                      NewTypeBy arity pos =>
                        pure $ applyNewType arity pos f' args'
                      EraseArgs arity epos =>
                        pure $ eraseConArgs arity epos f' args'
                      Arity a =>
                        pure $ expandToArity a f' args'

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
                        pure $ MkConAlt xn TYCON Nothing args !(toCExpTree n sc)
                                  :: !(conCases n ns)
           case (definition gdef) of
                DCon _ arity (Just pos) => conCases n ns -- skip it
                _ => do xn <- getFullName x
                        let (args' ** sub)
                            = mkDropSubst 0 (eraseArgs gdef) vars args
                        sc' <- toCExpTree n sc
                        ns' <- conCases n ns
                        if dcon (definition gdef)
                           then pure $ MkConAlt xn !(dconFlag xn) (Just tag) args' (shrinkCExp sub sc') :: ns'
                           else pure $ MkConAlt xn !(dconFlag xn) Nothing args' (shrinkCExp sub sc') :: ns'
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
                     if noworld -- just substitute the scrutinee into
                                -- the RHS
                        then
                             let (s, env) : (SizeOf args, SubstCEnv args vars)
                                     = mkSubst 0 scr pos args in
                              do log "compiler.newtype.world" 50 "Inlining case on \{show n} (no world)"
                                 pure $ Just (substs s env !(toCExpTree n sc))
                        else -- let bind the scrutinee, and substitute the
                             -- name into the RHS
                             let (s, env) : (_, SubstCEnv args (MN "eff" 0 :: vars))
                                     = mkSubst 0 (CLocal fc First) pos args in
                             do sc' <- toCExpTree n sc
                                let scope = insertNames {outer=args}
                                                        {inner=vars}
                                                        {ns = [MN "eff" 0]}
                                                        (mkSizeOf _) (mkSizeOf _) sc'
                                let tm = CLet fc (MN "eff" 0) NotInline scr (substs s env scope)
                                log "compiler.newtype.world" 50 "Kept the scrutinee \{show tm}"
                                pure (Just tm)
                _ => pure Nothing -- there's a normal match to do
    where
      mkSubst : Nat -> CExp vs ->
                Nat -> (args : List Name) -> (SizeOf args, SubstCEnv args vs)
      mkSubst _ _ _ [] = (zero, ScopeEmpty)
      mkSubst i scr pos (a :: as)
          = let (s, env) = mkSubst (1 + i) scr pos as in
            if i == pos
               then (suc s, scr :: env)
               else (suc s, CErased fc :: env)
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
              CLet fc arg YesInline (CForce fc LInf (CLocal (getLoc scTy) x)) $
              CLet fc ty YesInline (CErased fc)
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
                  then pure $ fromMaybe (CErased fc) def
                  else pure $ CConCase fc (CLocal fc x) cases def
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
  toCExpTree' n (STerm _ tm) = toCExp n tm
  toCExpTree' n (Unmatched msg)
      = pure $ CCrash emptyFC msg
  toCExpTree' n Impossible
      = pure $ CCrash emptyFC ("Impossible case encountered in " ++ show n)

-- Need this for ensuring that argument list matches up to operator arity for
-- builtins
data ArgList : Nat -> Scope -> Type where
     NoArgs : ArgList Z ScopeEmpty
     ConsArg : (a : Name) -> ArgList k as -> ArgList (S k) (a :: as)

mkArgList : Int -> (n : Nat) -> (ns ** ArgList n ns)
mkArgList i Z = (_ ** NoArgs)
mkArgList i (S k)
    = let (_ ** rec) = mkArgList (i + 1) k in
          (_ ** ConsArg (MN "arg" i) rec)

data NArgs : Type where
     User : Name -> List ClosedClosure -> NArgs
     Struct : String -> List (String, ClosedClosure) -> NArgs
     NUnit : NArgs
     NPtr : NArgs
     NGCPtr : NArgs
     NBuffer : NArgs
     NForeignObj : NArgs
     NIORes : ClosedClosure -> NArgs

getPArgs : {auto c : Ref Ctxt Defs} ->
           Defs -> ClosedClosure -> Core (String, ClosedClosure)
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
               Defs -> ClosedClosure -> Core (List (String, ClosedClosure))
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
           Defs -> Name -> List ClosedClosure -> Core NArgs
getNArgs defs (NS _ (UN $ Basic "IORes")) [arg] = pure $ NIORes arg
getNArgs defs (NS _ (UN $ Basic "Ptr")) [arg] = pure NPtr
getNArgs defs (NS _ (UN $ Basic "AnyPtr")) [] = pure NPtr
getNArgs defs (NS _ (UN $ Basic "GCPtr")) [arg] = pure NGCPtr
getNArgs defs (NS _ (UN $ Basic "GCAnyPtr")) [] = pure NGCPtr
getNArgs defs (NS _ (UN $ Basic "Buffer")) [] = pure NBuffer
getNArgs defs (NS _ (UN $ Basic "ForeignObj")) [] = pure NForeignObj
getNArgs defs (NS _ (UN $ Basic "Unit")) [] = pure NUnit
getNArgs defs (NS _ (UN $ Basic "Struct")) [n, args]
    = do NPrimVal _ (Str n') <- evalClosure defs n
             | nf => throw (GenericMsg (getLoc nf) "Unknown name for struct")
         pure (Struct n' !(getFieldArgs defs args))
getNArgs defs n args = pure $ User n args

nfToCFType : {auto c : Ref Ctxt Defs} ->
             FC -> (inStruct : Bool) -> ClosedNF -> Core CFType
nfToCFType _ _ (NPrimVal _ $ PrT IntType) = pure CFInt
nfToCFType _ _ (NPrimVal _ $ PrT IntegerType) = pure CFInteger
nfToCFType _ _ (NPrimVal _ $ PrT Bits8Type) = pure CFUnsigned8
nfToCFType _ _ (NPrimVal _ $ PrT Bits16Type) = pure CFUnsigned16
nfToCFType _ _ (NPrimVal _ $ PrT Bits32Type) = pure CFUnsigned32
nfToCFType _ _ (NPrimVal _ $ PrT Bits64Type) = pure CFUnsigned64
nfToCFType _ _ (NPrimVal _ $ PrT Int8Type) = pure CFInt8
nfToCFType _ _ (NPrimVal _ $ PrT Int16Type) = pure CFInt16
nfToCFType _ _ (NPrimVal _ $ PrT Int32Type) = pure CFInt32
nfToCFType _ _ (NPrimVal _ $ PrT Int64Type) = pure CFInt64
nfToCFType _ False (NPrimVal _ $ PrT StringType) = pure CFString
nfToCFType fc True (NPrimVal _ $ PrT StringType)
    = throw (GenericMsg fc "String not allowed in a foreign struct")
nfToCFType _ _ (NPrimVal _ $ PrT DoubleType) = pure CFDouble
nfToCFType _ _ (NPrimVal _ $ PrT CharType) = pure CFChar
nfToCFType _ _ (NPrimVal _ $ PrT WorldType) = pure CFWorld
nfToCFType _ False (NBind fc _ (Pi _ _ _ ty) sc)
    = do defs <- get Ctxt
         sty <- nfToCFType fc False !(evalClosure defs ty)
         sc' <- sc defs (toClosure defaultOpts ScopeEmpty (Erased fc Placeholder))
         tty <- nfToCFType fc False sc'
         pure (CFFun sty tty)
nfToCFType _ True (NBind fc _ _ _)
    = throw (GenericMsg fc "Function types not allowed in a foreign struct")
nfToCFType _ s (NTCon fc n_in _ _ args)
    = do defs <- get Ctxt
         n <- toFullNames n_in
         case !(getNArgs defs n $ toList (map snd args)) of
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
              NForeignObj => pure CFForeignObj
              NIORes uarg =>
                do narg <- evalClosure defs uarg
                   carg <- nfToCFType fc s narg
                   pure (CFIORes carg)
nfToCFType _ s (NType _ _)
    = pure (CFUser (UN (Basic "Type")) [])
nfToCFType _ s (NErased _ _)
    = pure (CFUser (UN (Basic "__")) [])
nfToCFType fc s t
    = do defs <- get Ctxt
         ty <- quote defs ScopeEmpty t
         throw (GenericMsg (getLoc t)
                       ("Can't marshal type for foreign call " ++
                                      show !(toFullNames ty)))

getCFTypes : {auto c : Ref Ctxt Defs} ->
             List CFType -> ClosedNF ->
             Core (List CFType, CFType)
getCFTypes args (NBind fc _ (Pi _ _ _ ty) sc)
    = do defs <- get Ctxt
         aty <- nfToCFType fc False !(evalClosure defs ty)
         sc' <- sc defs (toClosure defaultOpts ScopeEmpty (Erased fc Placeholder))
         getCFTypes (aty :: args) sc'
getCFTypes args t
    = pure (reverse args, !(nfToCFType (getLoc t) False t))

lamRHSenv : Int -> FC -> (ns : Scope) -> (SizeOf ns, SubstCEnv ns ScopeEmpty)
lamRHSenv i fc [] = (zero, ScopeEmpty)
lamRHSenv i fc (n :: ns)
    = let (s, env) = lamRHSenv (i + 1) fc ns in
      (suc s, CRef fc (MN "x" i) :: env)

mkBounds : (xs : _) -> Bounds xs
mkBounds [] = None
mkBounds (x :: xs) = Add x x (mkBounds xs)

getNewArgs : {done : _} ->
             SubstCEnv done args -> Scope
getNewArgs [] = []
getNewArgs (CRef _ n :: xs) = n :: getNewArgs xs
getNewArgs {done = x :: xs} (_ :: sub) = x :: getNewArgs sub

-- If a name is declared in one module and defined in another,
-- we have to assume arity 0 for incremental compilation because
-- we have no idea how it's defined, and when we made calls to the
-- function, they had arity 0.
lamRHS : (ns : Scope) -> CExp ns -> ClosedCExp
lamRHS ns tm
    = let (s, env) = lamRHSenv 0 (getFC tm) ns
          tmExp = substs s env (rewrite appendNilRightNeutral ns in tm)
          newArgs = reverse $ getNewArgs env
          bounds = mkBounds newArgs
          expLocs = mkLocals zero {vars = ScopeEmpty} bounds tmExp in
          lamBind (getFC tm) _ expLocs
  where
    lamBind : FC -> (ns : Scope) -> CExp ns -> ClosedCExp
    lamBind fc [] tm = tm
    lamBind fc (n :: ns) tm = lamBind fc ns (CLam fc n tm)

toCDef : Ref Ctxt Defs => Ref NextMN Int =>
         Name -> ClosedTerm -> List Nat -> Def ->
         Core CDef
toCDef n ty _ None
    = pure $ MkError $ CCrash emptyFC ("Encountered undefined name " ++ show !(getFullName n))
toCDef n ty erased (PMDef pi args _ tree _)
    = do let (args' ** p) = mkSub 0 args erased
         comptree <- toCExpTree n tree
         pure $ toLam (externalDecl pi) $ if isNil erased
            then MkFun args comptree
            else MkFun args' (shrinkCExp p comptree)
  where
    toLam : Bool -> CDef -> CDef
    toLam True (MkFun args rhs) = MkFun ScopeEmpty (lamRHS args rhs)
    toLam _ d = d
toCDef n ty _ (ExternDef arity)
    = let (ns ** args) = mkArgList 0 arity in
          pure $ MkFun _ (CExtPrim emptyFC !(getFullName n) (map toArgExp (getVars args)))
  where
    toArgExp : (Var ns) -> CExp ns
    toArgExp (MkVar p) = CLocal emptyFC p

    getVars : ArgList k ns -> List (Var ns)
    getVars NoArgs = []
    getVars (ConsArg a rest) = MkVar First :: map weakenVar (getVars rest)
toCDef n ty _ (ForeignDef arity cs)
    = do defs <- get Ctxt
         (atys, retty) <- getCFTypes [] !(nf defs ScopeEmpty ty)
         pure $ MkForeign cs atys retty
toCDef n ty _ (Builtin {arity} op)
    = let (ns ** args) = mkArgList 0 arity in
          pure $ MkFun _ (COp emptyFC op (map toArgExp (getVars args)))
  where
    toArgExp : (Var ns) -> CExp ns
    toArgExp (MkVar p) = CLocal emptyFC p

    getVars : ArgList k ns -> Vect k (Var ns)
    getVars NoArgs = []
    getVars (ConsArg a rest) = MkVar First :: map weakenVar (getVars rest)
toCDef n _ _ (DCon tag arity pos)
    = do let nt = snd <$> pos
         defs <- get Ctxt
         args <- numArgs {vars = ScopeEmpty} defs (Ref EmptyFC (DataCon tag arity) n)
         let arity' = case args of
                 NewTypeBy ar _ => ar
                 EraseArgs ar erased => ar `minus` length erased
                 Arity ar => ar
         pure $ MkCon (Just tag) arity' nt
toCDef n _ _ (TCon tag arity _ _ _ _ _ _)
    = pure $ MkCon Nothing arity Nothing
-- We do want to be able to compile these, but also report an error at run time
-- (and, TODO: warn at compile time)
toCDef n ty _ (Hole _ _)
    = pure $ MkError $ CCrash emptyFC ("Encountered unimplemented hole " ++
                                       show !(getFullName n))
toCDef n ty _ (Guess _ _ _)
    = pure $ MkError $ CCrash emptyFC ("Encountered constrained hole " ++
                                       show !(getFullName n))
toCDef n ty _ (BySearch _ _ _)
    = pure $ MkError $ CCrash emptyFC ("Encountered incomplete proof search " ++
                                       show !(getFullName n))
toCDef n ty _ def
    = pure $ MkError $ CCrash emptyFC ("Encountered uncompilable name " ++
                                       show (!(getFullName n), def))

export
compileExp : {auto c : Ref Ctxt Defs} ->
             ClosedTerm -> Core ClosedCExp
compileExp tm
    = do s <- newRef NextMN 0
         exp <- toCExp (UN $ Basic "main") tm
         constructorCExp exp

||| Given a name, look up an expression, and compile it to a CExp in the environment
export
compileDef : {auto c : Ref Ctxt Defs} -> Name -> Core ()
compileDef n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (InternalError ("Trying to compile unknown name " ++ show n))
         -- If we're incremental, and the name has no definition yet, it
         -- might end up defined in another module, so leave it, but warn
         if noDefYet (definition gdef) (incrementalCGs !getSession)
           -- This won't be accurate if we have names declared in one module
           -- and defined elsewhere. It's tricky to do the complete check that
           -- we do for whole program compilation, though, since that involves
           -- traversing everything from the main expression.
           -- For now, consider it an incentive not to have cycles :).
            then recordWarning (GenericWarn emptyFC ("Compiling hole " ++ show n))
            else do s <- newRef NextMN 0
                    ce <- toCDef n (type gdef) (eraseArgs gdef)
                           !(toFullNames (definition gdef))
                    ce <- constructorCDef ce
                    setCompiled n ce
  where
    noDefYet : Def -> List CG -> Bool
    noDefYet None (_ :: _) = True
    noDefYet _ _ = False
