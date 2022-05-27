module Idris.Resugar

import Core.Context
import Core.Context.Log
import Core.Env
import Core.Options

import Idris.Syntax
import Idris.Syntax.Traversals

import TTImp.TTImp
import TTImp.TTImp.Functor
import TTImp.Unelab
import TTImp.Utils


import Data.List1
import Data.List
import Data.Maybe
import Data.String
import Libraries.Data.StringMap

%default covering

-- Convert checked terms back to source syntax. Note that this is entirely
-- for readability therefore there is NO GUARANTEE that the result will
-- type check (in fact it probably won't due to tidying up names for
-- readability).

unbracketApp : PTerm' nm -> PTerm' nm
unbracketApp (PBracketed _ tm@(PApp _ _ _)) = tm
unbracketApp tm = tm

-- TODO: Deal with precedences
mkOp : {auto s : Ref Syn SyntaxInfo} ->
       IPTerm -> Core IPTerm
mkOp tm@(PApp fc (PApp _ (PRef opFC kn) x) y)
  = do syn <- get Syn
       let n = rawName kn
       let asOp = POp fc opFC kn (unbracketApp x) (unbracketApp y)
       case StringMap.lookup (snd $ displayName n) (infixes syn) of
         Just _ => pure asOp
         Nothing => case dropNS n of
           DN str _ => pure $ ifThenElse (isOpUserName (Basic str)) asOp tm
           _ => pure tm
mkOp tm@(PApp fc (PRef opFC kn) x)
  = do syn <- get Syn
       let n = rawName kn
       let asOp = PSectionR fc opFC (unbracketApp x) kn
       case StringMap.lookup (snd $ displayName n) (infixes syn) of
         Just _ => pure asOp
         Nothing => case dropNS n of
           DN str _ => pure $ ifThenElse (isOpUserName (Basic str)) asOp tm
           _ => pure tm
mkOp tm = pure tm

mkSectionL : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             IPTerm -> Core IPTerm
mkSectionL tm@(PLam fc rig info (PRef _ bd) ty
                 (PApp _ (PApp _ (PRef opFC kn) (PRef _ (MkKindedName (Just Bound) nm _))) x))
  = do log "resugar.sectionL" 30 $ "SectionL candidate: \{show tm}"
       let True = bd.fullName == nm
         | _ => pure tm
       syn <- get Syn
       let n = rawName kn
       let asOp = PSectionL fc opFC kn (unbracketApp x)
       case StringMap.lookup (snd $ displayName n) (infixes syn) of
         Just _ => pure asOp
         Nothing => case dropNS n of
           DN str _ => pure $ ifThenElse (isOpUserName (Basic str)) asOp tm
           _ => pure tm
mkSectionL tm = pure tm

export
addBracket : FC -> PTerm' nm -> PTerm' nm
addBracket fc tm = if needed tm then PBracketed fc tm else tm
  where
    needed : PTerm' nm -> Bool
    needed (PBracketed _ _) = False
    needed (PRef _ _) = False
    needed (PPair _ _ _) = False
    needed (PDPair _ _ _ _ _) = False
    needed (PUnit _) = False
    needed (PComprehension _ _ _) = False
    needed (PList _ _ _) = False
    needed (PSnocList _ _ _) = False
    needed (PRange{}) = False
    needed (PRangeStream{}) = False
    needed (PPrimVal _ _) = False
    needed (PIdiom{}) = False
    needed (PBang{}) = False
    needed tm = True

bracket : {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          (outer : Nat) -> (inner : Nat) ->
          IPTerm -> Core IPTerm
bracket outer inner tm
    = do tm <- mkOp tm
         tm <- mkSectionL tm
         if outer > inner
            then pure (addBracket emptyFC tm)
            else pure tm

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

unbracket : PTerm' nm -> PTerm' nm
unbracket (PBracketed _ tm) = tm
unbracket tm = tm

||| Attempt to extract a constant natural number
extractNat : Nat -> IPTerm -> Maybe Nat
extractNat acc tm = case tm of
  PRef _ (MkKindedName _ (NS ns (UN (Basic n))) rn) =>
    do guard (n == "Z")
       guard (ns == typesNS || ns == preludeNS)
       pure acc
  PApp _ (PRef _ (MkKindedName _ (NS ns (UN (Basic n))) rn)) k => case n of
    "S" => do guard (ns == typesNS || ns == preludeNS)
              extractNat (1 + acc) k
    "fromInteger" => extractNat acc k
    _ => Nothing
  PPrimVal _ (BI n) => do guard (0 <= n)
                          pure (acc + integerToNat n)
  PBracketed _ k    => extractNat acc k
  _                 => Nothing

||| Attempt to extract a constant integer
extractInteger : IPTerm -> Maybe Integer
extractInteger tm = case tm of
  PApp _ (PRef _ (MkKindedName _ (NS ns (UN (Basic n))) rn)) k => case n of
    "fromInteger" => extractInteger k
    "negate"      => negate <$> extractInteger k
    _ => Nothing
  PPrimVal _ (BI i) => pure i
  PBracketed _ t    => extractInteger t
  _                 => Nothing

||| Attempt to extract a constant double
extractDouble : IPTerm -> Maybe Double
extractDouble tm = case tm of
  PApp _ (PRef _ (MkKindedName _ (NS ns (UN (Basic n))) rn)) k => case n of
    "fromDouble" => extractDouble k
    "negate"     => negate <$> extractDouble k
    _ => Nothing
  PPrimVal _ (Db d) => pure d
  PBracketed _ t    => extractDouble t
  _                 => Nothing

mutual

  ||| Put the special names (Nil, ::, Pair, Z, S, etc) back as syntax
  ||| Returns `Nothing` in case there was nothing to resugar.
  sugarAppM : IPTerm -> Maybe IPTerm
  sugarAppM (PApp fc (PApp _ (PApp _ (PRef opFC (MkKindedName nt (NS ns nm) rn)) l) m) r) =
    case nameRoot nm of
      "rangeFromThenTo" => pure $ PRange fc (unbracket l) (Just $ unbracket m) (unbracket r)
      _ => Nothing
  sugarAppM (PApp fc (PApp _ (PRef opFC (MkKindedName nt (NS ns nm) rn)) l) r) =
    if builtinNS == ns then
      case nameRoot nm of
        "Pair"   => pure $ PPair fc (unbracket l) (unbracket r)
        "MkPair" => pure $ PPair fc (unbracket l) (unbracket r)
        "DPair"  => case unbracket r of
          PLam _ _ _ n _ r' => pure $ PDPair fc opFC n (unbracket l) (unbracket r')
          _                 => Nothing
        "Equal"  => pure $ PEq fc (unbracket l) (unbracket r)
        "==="    => pure $ PEq fc (unbracket l) (unbracket r)
        "~=~"    => pure $ PEq fc (unbracket l) (unbracket r)
        _        => Nothing
    else if dpairNS == ns then
      case nameRoot nm of
        "MkDPair" => pure $ PDPair fc opFC (unbracket l) (PImplicit opFC) (unbracket r)
        _                 => Nothing
    else
      case nameRoot nm of
        "::" => case sugarApp (unbracket r) of
          PList fc nilFC xs => pure $ PList fc nilFC ((opFC, unbracketApp l) :: xs)
          _ => Nothing
        ":<" => case sugarApp (unbracket l) of
          PSnocList fc nilFC xs => pure $ PSnocList fc nilFC
                                            (xs :< (opFC, unbracketApp r))
          _ => Nothing
        "rangeFromTo" => pure $ PRange fc (unbracket l) Nothing (unbracket r)
        "rangeFromThen" => pure $ PRangeStream fc (unbracket l) (Just $ unbracket r)
        _    => Nothing
  sugarAppM tm =
  -- refolding natural numbers if the expression is a constant
    let Nothing = extractNat 0 tm
          | Just k => pure $ PPrimVal (getPTermLoc tm) (BI (cast k))
        Nothing = extractInteger tm
          | Just k => pure $ PPrimVal (getPTermLoc tm) (BI k)
        Nothing = extractDouble tm
          | Just d => pure $ PPrimVal (getPTermLoc tm) (Db d)
    in case tm of
        PRef fc (MkKindedName nt (NS ns nm) rn) =>
          if builtinNS == ns
             then case nameRoot nm of
               "Unit"   => pure $ PUnit fc
               "MkUnit" => pure $ PUnit fc
               _           => Nothing
             else case nameRoot nm of
               "Nil" => pure $ PList fc fc []
               "Lin" => pure $ PSnocList fc fc [<]
               _     => Nothing
        PApp fc (PRef _ (MkKindedName nt (NS ns nm) rn)) arg =>
          case nameRoot nm of
            "rangeFrom" => pure $ PRangeStream fc (unbracket arg) Nothing
            _           => Nothing
        _ => Nothing

  ||| Put the special names (Nil, ::, Pair, Z, S, etc.) back as syntax

  sugarApp : IPTerm -> IPTerm
  sugarApp tm = fromMaybe tm (sugarAppM tm)

export
sugarName : Name -> String
sugarName (MN n _) = "(implicit) " ++ n
sugarName (PV n _) = sugarName n
sugarName (DN n _) = n
sugarName x = show x

toPRef : FC -> KindedName -> Core IPTerm
toPRef fc (MkKindedName nt fn nm) = case dropNS nm of
  MN n i     => pure (sugarApp (PRef fc (MkKindedName nt fn $ MN n i)))
  PV n _     => pure (sugarApp (PRef fc (MkKindedName nt fn $ n)))
  DN n _     => pure (sugarApp (PRef fc (MkKindedName nt fn $ UN $ Basic n)))
  Nested _ n => toPRef fc (MkKindedName nt fn n)
  n          => pure (sugarApp (PRef fc (MkKindedName nt fn n)))

mutual
  toPTerm : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            (prec : Nat) -> IRawImp -> Core IPTerm
  toPTerm p (IVar fc nm) = do
    t <- if fullNamespace !(getPPrint)
      then pure $ PRef fc nm
      else toPRef fc nm
    log "resugar.var" 70 $
      unwords [ "Resugaring", show @{Raw} nm.rawName, "to", show t]
    pure t
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
      needsBind (Just nm@(UN (Basic t)))
          = let ret = map rawName ret
                ns = findBindableNames False [] [] ret
                allNs = findAllNames [] ret in
                (nm `elem` allNs) && not (t `elem` (map Builtin.fst ns))
      needsBind _ = False
  toPTerm p (IPi fc rig pt n arg ret)
      = do arg' <- toPTerm appPrec arg
           ret' <- toPTerm tyPrec ret
           pt' <- traverse (toPTerm argPrec) pt
           bracket p tyPrec (PPi fc rig pt' n arg' ret')
  toPTerm p (ILam fc rig pt mn arg sc)
      = do let n = case mn of
                        Nothing => UN Underscore
                        Just n' => n'
           imp <- showImplicits
           arg' <- if imp then toPTerm tyPrec arg
                          else pure (PImplicit fc)
           sc' <- toPTerm startPrec sc
           pt' <- traverse (toPTerm argPrec) pt
           let var = PRef fc (MkKindedName (Just Bound) n n)
           bracket p startPrec (PLam fc rig pt' var arg' sc')
  toPTerm p (ILet fc lhsFC rig n ty val sc)
      = do imp <- showImplicits
           ty' <- if imp then toPTerm startPrec ty
                         else pure (PImplicit fc)
           val' <- toPTerm startPrec val
           sc' <- toPTerm startPrec sc
           let var = PRef lhsFC (MkKindedName (Just Bound) n n)
           bracket p startPrec (PLet fc rig var ty' val' sc' [])
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
      mkIf : IPTerm -> IPTerm
      mkIf tm@(PCase loc sc [MkPatClause _ (PRef _ tval) t [],
                             MkPatClause _ (PRef _ fval) f []])
         = if dropNS (rawName tval) == UN (Basic "True")
           && dropNS (rawName fval) == UN (Basic "False")
              then PIfThenElse loc sc t f
              else tm
      mkIf tm = tm
  toPTerm p (ILocal fc ds sc)
      = do ds' <- traverse toPDecl ds
           sc' <- toPTerm startPrec sc
           bracket p startPrec (PLocal fc (catMaybes ds') sc')
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
  toPTerm p (IBindVar fc v)
    = let nm = UN (Basic v) in
      pure (PRef fc (MkKindedName (Just Bound) nm nm))
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
           pure $ PQuoteDecl fc (catMaybes ds')
  toPTerm p (IUnquote fc tm) = pure (PUnquote fc !(toPTerm argPrec tm))
  toPTerm p (IRunElab fc tm) = pure (PRunElab fc !(toPTerm argPrec tm))

  toPTerm p (IUnifyLog fc _ tm) = toPTerm p tm
  toPTerm p (Implicit fc True) = pure (PImplicit fc)
  toPTerm p (Implicit fc False) = pure (PInfer fc)

  toPTerm p (IWithUnambigNames fc ns rhs) =
    PWithUnambigNames fc ns <$> toPTerm startPrec rhs

  mkApp : {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          IPTerm ->
          List (FC, Maybe (Maybe Name), IPTerm) ->
          Core IPTerm
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
               IRawImp -> List (FC, Maybe (Maybe Name), IPTerm) ->
               Core IPTerm
  toPTermApp (IApp fc f a) args
      = do a' <- toPTerm argPrec a
           toPTermApp f ((fc, Nothing, a') :: args)
  toPTermApp (INamedApp fc f n a) args
      = do a' <- toPTerm startPrec a
           toPTermApp f ((fc, Just (Just n), a') :: args)
  toPTermApp fn@(IVar fc n) args
      = do defs <- get Ctxt
           case !(lookupCtxtExact (rawName n) (gamma defs)) of
                Nothing => do fn' <- toPTerm appPrec fn
                              mkApp fn' args
                Just def => do fn' <- toPTerm appPrec fn
                               fenv <- showFullEnv
                               let args'
                                     = if fenv
                                          then args
                                          else drop (length (localVars def)) args
                               mkApp fn' args'
  toPTermApp fn args
      = do fn' <- toPTerm appPrec fn
           mkApp fn' args

  toPFieldUpdate : {auto c : Ref Ctxt Defs} ->
                   {auto s : Ref Syn SyntaxInfo} ->
                   IFieldUpdate' KindedName -> Core (PFieldUpdate' KindedName)
  toPFieldUpdate (ISetField p v)
      = do v' <- toPTerm startPrec v
           pure (PSetField p v')
  toPFieldUpdate (ISetFieldApp p v)
      = do v' <- toPTerm startPrec v
           pure (PSetFieldApp p v')

  toPClause : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              ImpClause' KindedName -> Core (PClause' KindedName)
  toPClause (PatClause fc lhs rhs)
      = pure (MkPatClause fc !(toPTerm startPrec lhs)
                             !(toPTerm startPrec rhs)
                             [])
  toPClause (WithClause fc lhs rig wval prf flags cs)
      = pure $ MkWithClause fc
                 !(toPTerm startPrec lhs)
                 (MkPWithProblem rig !(toPTerm startPrec wval) prf ::: [])
                 flags
                 !(traverse toPClause cs)
  toPClause (ImpossibleClause fc lhs)
      = pure (MkImpossible fc !(toPTerm startPrec lhs))

  toPTypeDecl : {auto c : Ref Ctxt Defs} ->
                {auto s : Ref Syn SyntaxInfo} ->
                ImpTy' KindedName -> Core (PTypeDecl' KindedName)
  toPTypeDecl (MkImpTy fc nameFC n ty)
      = pure (MkPTy fc nameFC n "" !(toPTerm startPrec ty))

  toPData : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            ImpData' KindedName -> Core (PDataDecl' KindedName)
  toPData (MkImpData fc n ty opts cs)
      = pure (MkPData fc n !(toPTerm startPrec ty) opts
                   !(traverse toPTypeDecl cs))
  toPData (MkImpLater fc n ty)
      = pure (MkPLater fc n !(toPTerm startPrec ty))

  toPField : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             IField' KindedName -> Core (PField' KindedName)
  toPField (MkIField fc c p n ty)
      = do ty' <- toPTerm startPrec ty
           p' <- traverse (toPTerm startPrec) p
           pure (MkField fc "" c p' n ty')

  toPRecord : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              ImpRecord' KindedName ->
              Core ( Name
                   , List (Name, RigCount, PiInfo IPTerm, IPTerm)
                   , Maybe Name
                   , List (PField' KindedName))
  toPRecord (MkImpRecord fc n ps con fs)
      = do ps' <- traverse (\ (n, c, p, ty) =>
                                   do ty' <- toPTerm startPrec ty
                                      p' <- mapPiInfo p
                                      pure (n, c, p', ty')) ps
           fs' <- traverse toPField fs
           pure (n, ps', Just con, fs')
    where
      mapPiInfo : PiInfo IRawImp -> Core (PiInfo IPTerm)
      mapPiInfo Explicit        = pure   Explicit
      mapPiInfo Implicit        = pure   Implicit
      mapPiInfo AutoImplicit    = pure   AutoImplicit
      mapPiInfo (DefImplicit p) = pure $ DefImplicit !(toPTerm startPrec p)

  toPFnOpt : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             FnOpt' KindedName -> Core (PFnOpt' KindedName)
  toPFnOpt (ForeignFn cs)
      = do cs' <- traverse (toPTerm startPrec) cs
           pure (PForeign cs')
  toPFnOpt o = pure $ IFnOpt o

  toPDecl : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            ImpDecl' KindedName -> Core (Maybe (PDecl' KindedName))
  toPDecl (IClaim fc rig vis opts ty)
      = do opts' <- traverse toPFnOpt opts
           pure (Just (PClaim fc rig vis opts' !(toPTypeDecl ty)))
  toPDecl (IData fc vis mbtot d)
      = pure (Just (PData fc "" vis mbtot !(toPData d)))
  toPDecl (IDef fc n cs)
      = pure (Just (PDef fc !(traverse toPClause cs)))
  toPDecl (IParameters fc ps ds)
      = do ds' <- traverse toPDecl ds
           pure (Just (PParameters fc
                        !(traverse (\(n, rig, info, tpe) =>
                            do info' <- traverse (toPTerm startPrec) info
                               tpe' <- toPTerm startPrec tpe
                               pure (n, rig, info', tpe')) ps)
                (catMaybes ds')))
  toPDecl (IRecord fc _ vis mbtot r)
      = do (n, ps, con, fs) <- toPRecord r
           pure (Just (PRecord fc "" vis mbtot n ps con fs))
  toPDecl (IFail fc msg ds)
      = do ds' <- traverse toPDecl ds
           pure (Just (PFail fc msg (catMaybes ds')))
  toPDecl (INamespace fc ns ds)
      = do ds' <- traverse toPDecl ds
           pure (Just (PNamespace fc ns (catMaybes ds')))
  toPDecl (ITransform fc n lhs rhs)
      = pure (Just (PTransform fc (show n)
                                  !(toPTerm startPrec lhs)
                                  !(toPTerm startPrec rhs)))
  toPDecl (IRunElabDecl fc tm)
      = pure (Just (PRunElabDecl fc !(toPTerm startPrec tm)))
  toPDecl (IPragma _ _) = pure Nothing
  toPDecl (ILog _) = pure Nothing
  toPDecl (IBuiltin fc type name) = pure $ Just $ PBuiltin fc type name

export
cleanPTerm : {auto c : Ref Ctxt Defs} ->
             IPTerm -> Core IPTerm
cleanPTerm ptm
   = do pp <- getPPrint
        if showMachineNames pp then pure ptm else mapPTermM cleanNode ptm

  where

    cleanName : Name -> Core Name
    cleanName nm = case nm of
      PV n _     => pure n
      -- Some of these may be "_" so we use `mkUserName`
      MN n _     => pure (UN $ mkUserName n)
      DN n _     => pure (UN $ mkUserName n)
      -- namespaces have already been stripped in toPTerm if necessary
      NS ns n    => NS ns <$> cleanName n
      Nested _ n => cleanName n
      UN n       => pure (UN n)
      _          => UN . mkUserName <$> prettyName nm

    cleanKindedName : KindedName -> Core KindedName
    cleanKindedName (MkKindedName nt fn nm) = MkKindedName nt fn <$> cleanName nm

    cleanBinderName : PiInfo IPTerm -> Name -> Core (Maybe Name)
    cleanBinderName AutoImplicit (UN (Basic "__con")) = pure Nothing
    cleanBinderName _ nm = Just <$> cleanName nm

    cleanNode : IPTerm -> Core IPTerm
    cleanNode (PRef fc nm)    =
      PRef fc <$> cleanKindedName nm
    cleanNode (POp fc opFC op x y) =
      (\ op => POp fc opFC op x y) <$> cleanKindedName op
    cleanNode (PPrefixOp fc opFC op x) =
      (\ op => PPrefixOp fc opFC op x) <$> cleanKindedName op
    cleanNode (PSectionL fc opFC op x) =
      (\ op => PSectionL fc opFC op x) <$> cleanKindedName op
    cleanNode (PSectionR fc opFC x op) =
      PSectionR fc opFC x <$> cleanKindedName op
    cleanNode (PPi fc rig vis (Just n) arg ret) =
      (\ n => PPi fc rig vis n arg ret) <$> cleanBinderName vis n
    cleanNode tm = pure tm

toCleanPTerm : {auto c : Ref Ctxt Defs} ->
               {auto s : Ref Syn SyntaxInfo} ->
               (prec : Nat) -> IRawImp -> Core IPTerm
toCleanPTerm prec tti = do
  ptm <- toPTerm prec tti
  cleanPTerm ptm

export
resugar : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          Env Term vars -> Term vars -> Core IPTerm
resugar env tm
    = do tti <- unelab env tm
         toCleanPTerm startPrec tti

export
resugarNoPatvars : {vars : _} ->
                   {auto c : Ref Ctxt Defs} ->
                   {auto s : Ref Syn SyntaxInfo} ->
                   Env Term vars -> Term vars -> Core IPTerm
resugarNoPatvars env tm
    = do tti <- unelabNoPatvars env tm
         toCleanPTerm startPrec tti

export
pterm : {auto c : Ref Ctxt Defs} ->
        {auto s : Ref Syn SyntaxInfo} ->
        IRawImp -> Core IPTerm
pterm raw = toCleanPTerm startPrec raw
