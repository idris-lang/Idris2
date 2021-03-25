module Idris.Resugar

import Core.Context
import Core.Env
import Core.Options

import Idris.Syntax

import TTImp.TTImp
import TTImp.Unelab
import TTImp.Utils

import Data.List
import Data.List1
import Data.Maybe
import Libraries.Data.StringMap

%default covering

-- Convert checked terms back to source syntax. Note that this is entirely
-- for readability therefore there is NO GUARANTEE that the result will
-- type check (in fact it probably won't due to tidying up names for
-- readability).

unbracketApp : PTerm -> PTerm
unbracketApp (PBracketed _ tm@(PApp _ _ _)) = tm
unbracketApp tm = tm

-- TODO: Deal with precedences
mkOp : {auto s : Ref Syn SyntaxInfo} ->
       PTerm -> Core PTerm
mkOp tm@(PApp fc (PApp _ (PRef _ n) x) y)
    = do syn <- get Syn
         case StringMap.lookup (nameRoot n) (infixes syn) of
              Nothing => pure tm
              Just _ => pure (POp fc n (unbracketApp x) (unbracketApp y))
mkOp tm = pure tm

export
addBracket : FC -> PTerm -> PTerm
addBracket fc tm = if needed tm then PBracketed fc tm else tm
  where
    needed : PTerm -> Bool
    needed (PBracketed _ _) = False
    needed (PRef _ _) = False
    needed (PPair _ _ _) = False
    needed (PDPair _ _ _ _) = False
    needed (PUnit _) = False
    needed (PComprehension _ _ _) = False
    needed (PList _ _) = False
    needed (PPrimVal _ _) = False
    needed tm = True

bracket : {auto s : Ref Syn SyntaxInfo} ->
          (outer : Nat) -> (inner : Nat) -> PTerm -> Core PTerm
bracket outer inner tm
    = do tm' <- mkOp tm
         if outer > inner
            then pure (addBracket emptyFC tm')
            else pure tm'

startPrec : Nat
startPrec = 0

tyPrec : Nat
tyPrec = 1

appPrec : Nat
appPrec = 999

argPrec : Nat
argPrec = 1000

showImplicits : {auto c : Ref Ctxt Defs} ->
                Core Bool
showImplicits
    = do pp <- getPPrint
         pure (showImplicits pp)

showFullEnv : {auto c : Ref Ctxt Defs} ->
              Core Bool
showFullEnv
    = do pp <- getPPrint
         pure (showFullEnv pp)

fullNamespace : {auto c : Ref Ctxt Defs} ->
                Core Bool
fullNamespace
    = do pp <- getPPrint
         pure (fullNamespace pp)

unbracket : PTerm -> PTerm
unbracket (PBracketed _ tm) = tm
unbracket tm = tm

||| Attempt to extract a constant natural number
extractNat : Nat -> PTerm -> Maybe Nat
extractNat acc tm = case tm of
  PRef _ (NS ns (UN n)) =>
    do guard (n == "Z")
       guard (ns == typesNS || ns == preludeNS)
       pure acc
  PApp _ (PRef _ (NS ns (UN n))) k => do
    do guard (n == "S")
       guard (ns == typesNS || ns == preludeNS)
       extractNat (1 + acc) k
  PPrimVal _ (BI n) => pure (acc + integerToNat n)
  PBracketed _ k    => extractNat acc k
  _                 => Nothing

mutual

  ||| Put the special names (Nil, ::, Pair, Z, S, etc) back as syntax
  ||| Returns `Nothing` in case there was nothing to resugar.
  sugarAppM : PTerm -> Maybe PTerm
  sugarAppM (PApp fc (PApp _ (PRef _ (NS ns nm)) l) r) =
    if builtinNS == ns
       then case nameRoot nm of
         "Pair"   => pure $ PPair fc (unbracket l) (unbracket r)
         "MkPair" => pure $ PPair fc (unbracket l) (unbracket r)
         "DPair"  => case unbracket r of
            PLam _ _ _ n _ r' => pure $ PDPair fc n (unbracket l) (unbracket r')
            _                 => Nothing
         "Equal"  => pure $ PEq fc (unbracket l) (unbracket r)
         "==="    => pure $ PEq fc (unbracket l) (unbracket r)
         "~=~"    => pure $ PEq fc (unbracket l) (unbracket r)
         _        => Nothing
       else if nameRoot nm == "::"
               then case sugarApp (unbracket r) of
                 PList fc xs => pure $ PList fc (unbracketApp l :: xs)
                 _           => Nothing
               else Nothing
  sugarAppM tm =
  -- refolding natural numbers if the expression is a constant
    case extractNat 0 tm of
      Just k  => pure $ PPrimVal (getPTermLoc tm) (BI (cast k))
      Nothing => case tm of
        PRef fc (NS ns nm) =>
          if builtinNS == ns
             then case nameRoot nm of
               "Unit"   => pure $ PUnit fc
               "MkUnit" => pure $ PUnit fc
               _           => Nothing
             else if nameRoot nm == "Nil"
                     then pure $ PList fc []
                     else Nothing
        _ => Nothing

  ||| Put the special names (Nil, ::, Pair, Z, S, etc.) back as syntax

  sugarApp : PTerm -> PTerm
  sugarApp tm = fromMaybe tm (sugarAppM tm)

export
sugarName : Name -> String
sugarName (MN n _) = "(implicit) " ++ n
sugarName (PV n _) = sugarName n
sugarName (DN n _) = n
sugarName x = show x

toPRef : FC -> Name -> Core PTerm
toPRef fc nm = case nm of
  MN n _     => pure (sugarApp (PRef fc (UN n)))
  PV n _     => pure (sugarApp (PRef fc n))
  DN n _     => pure (sugarApp (PRef fc (UN n)))
  Nested _ n => toPRef fc n
  _          => pure (sugarApp (PRef fc nm))

mutual
  toPTerm : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            (prec : Nat) -> RawImp -> Core PTerm
  toPTerm p (IVar fc nm) = if fullNamespace !(getPPrint)
                             then pure $ PRef fc nm
                             else toPRef fc nm
  toPTerm p (IPi fc rig Implicit n arg ret)
      = do imp <- showImplicits
           if imp
              then do arg' <- toPTerm tyPrec arg
                      ret' <- toPTerm tyPrec ret
                      bracket p tyPrec (PPi fc rig Implicit n arg' ret')
              else if needsBind n
                      then do arg' <- toPTerm tyPrec arg
                              ret' <- toPTerm tyPrec ret
                              bracket p tyPrec (PPi fc rig Implicit n arg' ret')
                      else toPTerm p ret
    where
      needsBind : Maybe Name -> Bool
      needsBind (Just (UN t))
          = let ns = findBindableNames False [] [] ret
                allNs = findAllNames [] ret in
                ((UN t) `elem` allNs) && not (t `elem` (map Builtin.fst ns))
      needsBind _ = False
  toPTerm p (IPi fc rig pt n arg ret)
      = do arg' <- toPTerm appPrec arg
           ret' <- toPTerm tyPrec ret
           pt' <- traverse (toPTerm argPrec) pt
           bracket p tyPrec (PPi fc rig pt' n arg' ret')
  toPTerm p (ILam fc rig pt mn arg sc)
      = do let n = case mn of
                        Nothing => UN "_"
                        Just n' => n'
           imp <- showImplicits
           arg' <- if imp then toPTerm tyPrec arg
                          else pure (PImplicit fc)
           sc' <- toPTerm startPrec sc
           pt' <- traverse (toPTerm argPrec) pt
           bracket p startPrec (PLam fc rig pt' (PRef fc n) arg' sc')
  toPTerm p (ILet fc lhsFC rig n ty val sc)
      = do imp <- showImplicits
           ty' <- if imp then toPTerm startPrec ty
                         else pure (PImplicit fc)
           val' <- toPTerm startPrec val
           sc' <- toPTerm startPrec sc
           bracket p startPrec (PLet fc rig (PRef lhsFC n)
                                     ty' val' sc' [])
  toPTerm p (ICase fc sc scty [PatClause _ lhs rhs])
      = do sc' <- toPTerm startPrec sc
           lhs' <- toPTerm startPrec lhs
           rhs' <- toPTerm startPrec rhs
           bracket p startPrec
                   (PLet fc top lhs' (PImplicit fc) sc' rhs' [])
  toPTerm p (ICase fc sc scty alts)
      = do sc' <- toPTerm startPrec sc
           alts' <- traverse toPClause alts
           bracket p startPrec (mkIf (PCase fc sc' alts'))
    where
      mkIf : PTerm -> PTerm
      mkIf tm@(PCase loc sc [MkPatClause _ (PRef _ tval) t [],
                             MkPatClause _ (PRef _ fval) f []])
         = if dropNS tval == UN "True" && dropNS fval == UN "False"
              then PIfThenElse loc sc t f
              else tm
      mkIf tm = tm
  toPTerm p (ILocal fc ds sc)
      = do ds' <- traverse toPDecl ds
           sc' <- toPTerm startPrec sc
           bracket p startPrec (PLocal fc (mapMaybe id ds') sc')
  toPTerm p (ICaseLocal fc _ _ _ sc) = toPTerm p sc
  toPTerm p (IUpdate fc ds f)
      = do ds' <- traverse toPFieldUpdate ds
           f' <- toPTerm argPrec f
           bracket p startPrec (PApp fc (PUpdate fc ds') f')
  toPTerm p (IApp fc fn arg)
      = do arg' <- toPTerm argPrec arg
           app <- toPTermApp fn [(fc, Nothing, arg')]
           bracket p appPrec app
  toPTerm p (IAutoApp fc fn arg)
      = do arg' <- toPTerm argPrec arg
           app <- toPTermApp fn [(fc, Just Nothing, arg')]
           bracket p appPrec app
  toPTerm p (IWithApp fc fn arg)
      = do arg' <- toPTerm startPrec arg
           fn' <- toPTerm startPrec fn
           bracket p appPrec (PWithApp fc fn' arg')
  toPTerm p (INamedApp fc fn n arg)
      = do arg' <- toPTerm startPrec arg
           app <- toPTermApp fn [(fc, Just (Just n), arg')]
           imp <- showImplicits
           if imp
              then bracket p startPrec app
              else mkOp app
  toPTerm p (ISearch fc d) = pure (PSearch fc d)
  toPTerm p (IAlternative fc _ _) = pure (PImplicit fc)
  toPTerm p (IRewrite fc rule tm)
      = pure (PRewrite fc !(toPTerm startPrec rule)
                               !(toPTerm startPrec tm))
  toPTerm p (ICoerced fc tm) = toPTerm p tm
  toPTerm p (IPrimVal fc c) = pure (PPrimVal fc c)
  toPTerm p (IHole fc str) = pure (PHole fc False str)
  toPTerm p (IType fc) = pure (PType fc)
  toPTerm p (IBindVar fc v) = pure (PRef fc (UN v))
  toPTerm p (IBindHere fc _ tm) = toPTerm p tm
  toPTerm p (IAs fc nameFC _ n pat) = pure (PAs fc nameFC n !(toPTerm argPrec pat))
  toPTerm p (IMustUnify fc r pat) = pure (PDotted fc !(toPTerm argPrec pat))

  toPTerm p (IDelayed fc r ty) = pure (PDelayed fc r !(toPTerm argPrec ty))
  toPTerm p (IDelay fc tm) = pure (PDelay fc !(toPTerm argPrec tm))
  toPTerm p (IForce fc tm) = pure (PForce fc !(toPTerm argPrec tm))
  toPTerm p (IQuote fc tm) = pure (PQuote fc !(toPTerm argPrec tm))
  toPTerm p (IQuoteName fc n) = pure (PQuoteName fc n)
  toPTerm p (IQuoteDecl fc ds)
      = do ds' <- traverse toPDecl ds
           pure $ PQuoteDecl fc (mapMaybe id ds')
  toPTerm p (IUnquote fc tm) = pure (PUnquote fc !(toPTerm argPrec tm))
  toPTerm p (IRunElab fc tm) = pure (PRunElab fc !(toPTerm argPrec tm))

  toPTerm p (IUnifyLog fc _ tm) = toPTerm p tm
  toPTerm p (Implicit fc True) = pure (PImplicit fc)
  toPTerm p (Implicit fc False) = pure (PInfer fc)

  toPTerm p (IWithUnambigNames fc ns rhs) =
    PWithUnambigNames fc ns <$> toPTerm startPrec rhs

  mkApp : {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          PTerm -> List (FC, Maybe (Maybe Name), PTerm) -> Core PTerm
  mkApp fn [] = pure fn
  mkApp fn ((fc, Nothing, arg) :: rest)
      = do let ap = sugarApp (PApp fc fn arg)
           mkApp ap rest
  mkApp fn ((fc, Just Nothing, arg) :: rest)
      = do let ap = sugarApp (PAutoApp fc fn arg)
           mkApp ap rest
  mkApp fn ((fc, Just (Just n), arg) :: rest)
      = do imp <- showImplicits
           if imp
              then do let ap = PNamedApp fc fn n arg
                      mkApp ap rest
              else mkApp fn rest

  toPTermApp : {auto c : Ref Ctxt Defs} ->
               {auto s : Ref Syn SyntaxInfo} ->
               RawImp -> List (FC, Maybe (Maybe Name), PTerm) ->
               Core PTerm
  toPTermApp (IApp fc f a) args
      = do a' <- toPTerm argPrec a
           toPTermApp f ((fc, Nothing, a') :: args)
  toPTermApp (INamedApp fc f n a) args
      = do a' <- toPTerm startPrec a
           toPTermApp f ((fc, Just (Just n), a') :: args)
  toPTermApp fn@(IVar fc n) args
      = do defs <- get Ctxt
           case !(lookupCtxtExact n (gamma defs)) of
                Nothing => do fn' <- toPTerm appPrec fn
                              mkApp fn' args
                Just def => do fn' <- toPTerm appPrec fn
                               fenv <- showFullEnv
                               let args'
                                     = if fenv
                                          then args
                                          else drop (length (vars def)) args
                               mkApp fn' args'
  toPTermApp fn args
      = do fn' <- toPTerm appPrec fn
           mkApp fn' args

  toPFieldUpdate : {auto c : Ref Ctxt Defs} ->
                   {auto s : Ref Syn SyntaxInfo} ->
                   IFieldUpdate -> Core PFieldUpdate
  toPFieldUpdate (ISetField p v)
      = do v' <- toPTerm startPrec v
           pure (PSetField p v')
  toPFieldUpdate (ISetFieldApp p v)
      = do v' <- toPTerm startPrec v
           pure (PSetFieldApp p v')

  toPClause : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              ImpClause -> Core PClause
  toPClause (PatClause fc lhs rhs)
      = pure (MkPatClause fc !(toPTerm startPrec lhs)
                             !(toPTerm startPrec rhs)
                             [])
  toPClause (WithClause fc lhs rhs prf flags cs)
      = pure (MkWithClause fc !(toPTerm startPrec lhs)
                              !(toPTerm startPrec rhs)
                              prf
                              flags
                              !(traverse toPClause cs))
  toPClause (ImpossibleClause fc lhs)
      = pure (MkImpossible fc !(toPTerm startPrec lhs))

  toPTypeDecl : {auto c : Ref Ctxt Defs} ->
                {auto s : Ref Syn SyntaxInfo} ->
                ImpTy -> Core PTypeDecl
  toPTypeDecl (MkImpTy fc nameFC n ty)
      = pure (MkPTy fc nameFC n "" !(toPTerm startPrec ty))

  toPData : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            ImpData -> Core PDataDecl
  toPData (MkImpData fc n ty opts cs)
      = pure (MkPData fc n !(toPTerm startPrec ty) opts
                   !(traverse toPTypeDecl cs))
  toPData (MkImpLater fc n ty)
      = pure (MkPLater fc n !(toPTerm startPrec ty))

  toPField : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             IField -> Core PField
  toPField (MkIField fc c p n ty)
      = do ty' <- toPTerm startPrec ty
           p' <- traverse (toPTerm startPrec) p
           pure (MkField fc "" c p' n ty')

  toPRecord : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              ImpRecord ->
              Core (Name, List (Name, RigCount, PiInfo PTerm, PTerm), Maybe Name, List PField)
  toPRecord (MkImpRecord fc n ps con fs)
      = do ps' <- traverse (\ (n, c, p, ty) =>
                                   do ty' <- toPTerm startPrec ty
                                      p' <- mapPiInfo p
                                      pure (n, c, p', ty')) ps
           fs' <- traverse toPField fs
           pure (n, ps', Just con, fs')
    where
      mapPiInfo : PiInfo RawImp -> Core (PiInfo PTerm)
      mapPiInfo Explicit        = pure   Explicit
      mapPiInfo Implicit        = pure   Implicit
      mapPiInfo AutoImplicit    = pure   AutoImplicit
      mapPiInfo (DefImplicit p) = pure $ DefImplicit !(toPTerm startPrec p)

  toPFnOpt : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             FnOpt -> Core PFnOpt
  toPFnOpt (ForeignFn cs)
      = do cs' <- traverse (toPTerm startPrec) cs
           pure (PForeign cs')
  toPFnOpt o = pure $ IFnOpt o

  toPDecl : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            ImpDecl -> Core (Maybe PDecl)
  toPDecl (IClaim fc rig vis opts ty)
      = do opts' <- traverse toPFnOpt opts
           pure (Just (PClaim fc rig vis opts' !(toPTypeDecl ty)))
  toPDecl (IData fc vis d)
      = pure (Just (PData fc "" vis !(toPData d)))
  toPDecl (IDef fc n cs)
      = pure (Just (PDef fc !(traverse toPClause cs)))
  toPDecl (IParameters fc ps ds)
      = do ds' <- traverse toPDecl ds
           pure (Just (PParameters fc
                !(traverse (\ntm => do tm' <- toPTerm startPrec (snd ntm)
                                       pure (fst ntm, tm')) ps)
                (mapMaybe id ds')))
  toPDecl (IRecord fc _ vis r)
      = do (n, ps, con, fs) <- toPRecord r
           pure (Just (PRecord fc "" vis n ps con fs))
  toPDecl (INamespace fc ns ds)
      = do ds' <- traverse toPDecl ds
           pure (Just (PNamespace fc ns (mapMaybe id ds')))
  toPDecl (ITransform fc n lhs rhs)
      = pure (Just (PTransform fc (show n)
                                  !(toPTerm startPrec lhs)
                                  !(toPTerm startPrec rhs)))
  toPDecl (IRunElabDecl fc tm)
      = pure (Just (PRunElabDecl fc !(toPTerm startPrec tm)))
  toPDecl (IPragma _ _) = pure Nothing
  toPDecl (ILog _) = pure Nothing

export
cleanPTerm : {auto c : Ref Ctxt Defs} ->
             PTerm -> Core PTerm
cleanPTerm ptm
   = do ns <- fullNamespace
        if ns then pure ptm else mapPTermM cleanNode ptm

  where

    cleanName : Name -> Core Name
    cleanName nm = case nm of
      MN n _            => pure (UN n)
      PV n _            => pure n
      DN n _            => pure (UN n)
      NS _ (Nested _ n) => cleanName n
      _                 => UN <$> prettyName nm

    cleanNode : PTerm -> Core PTerm
    cleanNode (PRef fc nm)    =
      PRef fc <$> cleanName nm
    cleanNode (POp fc op x y) =
      (\ op => POp fc op x y) <$> cleanName op
    cleanNode (PPrefixOp fc op x) =
      (\ op => PPrefixOp fc op x) <$> cleanName op
    cleanNode (PSectionL fc op x) =
      (\ op => PSectionL fc op x) <$> cleanName op
    cleanNode (PSectionR fc x op) =
      PSectionR fc x <$> cleanName op
    cleanNode tm = pure tm

toCleanPTerm : {auto c : Ref Ctxt Defs} ->
               {auto s : Ref Syn SyntaxInfo} ->
               (prec : Nat) -> RawImp -> Core PTerm
toCleanPTerm prec tti = do
  ptm <- toPTerm prec tti
  cleanPTerm ptm

export
resugar : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          Env Term vars -> Term vars -> Core PTerm
resugar env tm
    = do tti <- unelab env tm
         toCleanPTerm startPrec tti

export
resugarNoPatvars : {vars : _} ->
                   {auto c : Ref Ctxt Defs} ->
                   {auto s : Ref Syn SyntaxInfo} ->
                   Env Term vars -> Term vars -> Core PTerm
resugarNoPatvars env tm
    = do tti <- unelabNoPatvars env tm
         toCleanPTerm startPrec tti

export
pterm : {auto c : Ref Ctxt Defs} ->
        {auto s : Ref Syn SyntaxInfo} ->
        RawImp -> Core PTerm
pterm raw = toCleanPTerm startPrec raw
