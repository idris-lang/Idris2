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
import Libraries.Data.ANameMap

%default covering

-- Convert checked terms back to source syntax. Note that this is entirely
-- for readability therefore there is NO GUARANTEE that the result will
-- type check (in fact it probably won't due to tidying up names for
-- readability).

unbracketApp : PTerm' nm -> PTerm' nm
unbracketApp (PBracketed _ tm@(PApp {})) = tm
unbracketApp tm = tm

-- TODO: Deal with precedences
mkOp : {auto s : Ref Syn SyntaxInfo} ->
       IPTerm -> Core IPTerm
mkOp tm@(PApp fc (PApp _ (PRef opFC kn) x) y)
  = do syn <- get Syn
       let raw = rawName kn
       let pop = if isOpName raw then OpSymbols else Backticked
       -- to check if the name is an operator we use the root name as a basic
       -- user name. This is because if the name is qualified with the namespace
       -- looking the fixity context will fail. A qualified operator would look
       -- like this: `M1.M2.(++)` which would not match its fixity namesapce
       -- that looks like this: `M1.M2.infixl.(++)`. However, since we only want
       -- to know if the name is an operator or not, it's enough to check
       -- that the fixity context contains the name `(++)`
       let rootName = UN (Basic (nameRoot raw))
       let asOp = POp fc (MkFCVal opFC
                $ NoBinder (unbracketApp x)) (MkFCVal opFC (pop kn)) (unbracketApp y)
       if not (null (lookupName rootName (infixes syn)))
         then pure asOp
         else case dropNS raw of
           DN str _ => pure $ ifThenElse (isOpUserName (Basic str)) asOp tm
           _ => pure tm
mkOp tm@(PApp fc (PRef opFC kn) x)
  = do syn <- get Syn
       let n = rawName kn
       let asOp = PSectionR fc (unbracketApp x) (MkFCVal opFC $ OpSymbols kn)
       if not (null $ lookupName (UN $ Basic (nameRoot n)) (infixes syn))
         then pure asOp
         else case dropNS n of
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
       let asOp = PSectionL fc (MkFCVal opFC $ OpSymbols kn) (unbracketApp x)
       if not (null $ lookupName (UN $ Basic (nameRoot n)) (fixities syn))
         then pure asOp
         else case dropNS n of
           DN str _ => pure $ ifThenElse (isOpUserName (Basic str)) asOp tm
           _ => pure tm
mkSectionL tm = pure tm

export
addBracket : FC -> PTerm' nm -> PTerm' nm
addBracket fc tm = if needed tm then PBracketed fc tm else tm
  where
    needed : PTerm' nm -> Bool
    needed (PBracketed {}) = False
    needed (PRef {}) = False
    needed (PPair {}) = False
    needed (PDPair {}) = False
    needed (PUnit {}) = False
    needed (PComprehension {}) = False
    needed (PList {}) = False
    needed (PSnocList {}) = False
    needed (PRange {}) = False
    needed (PRangeStream {}) = False
    needed (PPrimVal {}) = False
    needed (PIdiom {}) = False
    needed (PBang {}) = False
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
        "Equal"  => pure $ PEq fc (unbracket l) (unbracket r)
        "==="    => pure $ PEq fc (unbracket l) (unbracket r)
        "~=~"    => pure $ PEq fc (unbracket l) (unbracket r)
        _        => Nothing
    else if dpairNS == ns then
      case nameRoot nm of
        "DPair"  => case unbracket r of
          PLam _ _ _ n _ r' => pure $ PDPair fc opFC n (unbracket l) (unbracket r')
          _                 => Nothing
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
      needsBind (Just nm@(UN (Basic _)))
          = let ret = map rawName ret
                ns = findBindableNames False [] [] ret
                allNs = findAllNames [] ret in
                (nm `elem` allNs) && not (nm `elem` (map Builtin.fst ns))
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
  toPTerm p (ICase fc _ sc scty [PatClause _ lhs rhs])
      = do sc' <- toPTerm startPrec sc
           lhs' <- toPTerm startPrec lhs
           rhs' <- toPTerm startPrec rhs
           bracket p startPrec
                   (PLet fc top lhs' (PImplicit fc) sc' rhs' [])
  toPTerm p (ICase fc opts sc scty alts)
      = do opts' <- traverse toPFnOpt opts
           sc' <- toPTerm startPrec sc
           alts' <- traverse toPClause alts
           bracket p startPrec (mkIf (PCase fc opts' sc' alts'))
    where
      mkIf : IPTerm -> IPTerm
      mkIf tm@(PCase loc opts sc
                 [ MkPatClause _ (PRef _ tval) t []
                 , MkPatClause _ (PRef _ fval) f []])
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
  toPTerm p (IBindVar fc nm)
    = pure (PRef fc (MkKindedName (Just Bound) nm nm))
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
  toPTerm p (IRunElab fc _ tm) = pure (PRunElab fc !(toPTerm argPrec tm))

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
  toPTypeDecl impTy
      = pure (MkFCVal impTy.fc $ MkPTy (pure ("", impTy.tyName)) "" !(toPTerm startPrec impTy.val))

  toPData : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            ImpData' KindedName -> Core (PDataDecl' KindedName)
  toPData (MkImpData fc n ty opts cs)
      = pure (MkPData fc n !(traverseOpt (toPTerm startPrec) ty) opts
                   !(traverse toPTypeDecl cs))
  toPData (MkImpLater fc n ty)
      = pure (MkPLater fc n !(toPTerm startPrec ty))

  toPField : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             IField' KindedName -> Core (PField' KindedName)
  toPField field
      = do bind' <- traverse (toPTerm startPrec) field.val
           pure (Mk [field.fc , "", field.rig, [field.name]] bind')

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
  toPDecl (IClaim (MkWithData fc $ MkIClaimData rig vis opts ty))
      = do opts' <- traverse toPFnOpt opts
           pure (Just (MkWithData fc $ PClaim (MkPClaim rig vis opts' !(toPTypeDecl ty))))
  toPDecl (IData fc vis mbtot d)
      = pure (Just (MkFCVal fc $ PData "" vis mbtot !(toPData d)))
  toPDecl (IDef fc n cs)
      = pure (Just (MkFCVal fc $ PDef !(traverse toPClause cs)))
  toPDecl (IParameters fc ps ds)
      = do ds' <- traverse toPDecl ds
           args <-
             traverseList1 (\binder =>
                 do info' <- traverse (toPTerm startPrec) binder.val.info
                    type' <- toPTerm startPrec binder.val.boundType
                    pure (MkFullBinder info' binder.rig binder.name type')) ps
           pure (Just (MkFCVal fc (PParameters (Right args) (catMaybes ds'))))
  toPDecl (IRecord fc _ vis mbtot (MkWithData _ $ MkImpRecord header body))
      = do ps' <- traverse (traverse (traverse (toPTerm startPrec))) header.val
           fs' <- traverse toPField body.val
           pure (Just (MkFCVal fc $ PRecord "" vis mbtot
                          (MkPRecord header.name.val (map toBinder ps') body.opts (Just (AddDef body.name)) fs')))
           where
             toBinder : ImpParameter' (PTerm' KindedName) -> PBinder' KindedName
             toBinder binder
               = MkFullBinder binder.val.info binder.rig binder.name binder.val.boundType

  toPDecl (IFail fc msg ds)
      = do ds' <- traverse toPDecl ds
           pure (Just (MkFCVal fc $ PFail msg (catMaybes ds')))
  toPDecl (INamespace fc ns ds)
      = do ds' <- traverse toPDecl ds
           pure (Just (MkFCVal fc $ PNamespace ns (catMaybes ds')))
  toPDecl (ITransform fc n lhs rhs)
      = pure (Just (MkFCVal fc $ PTransform (show n)
                                  !(toPTerm startPrec lhs)
                                  !(toPTerm startPrec rhs)))
  toPDecl (IRunElabDecl fc tm)
      = pure (Just (MkFCVal fc $ PRunElabDecl !(toPTerm startPrec tm)))
  toPDecl (IPragma {}) = pure Nothing
  toPDecl (ILog _) = pure Nothing
  toPDecl (IBuiltin fc type name) = pure $ Just $ MkFCVal fc $ PBuiltin type name

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
    cleanNode (POp fc abi op y) =
      (\ op => POp fc abi op y) <$> traverse (traverseOp @{Functor.CORE} cleanKindedName) op
    cleanNode (PPrefixOp fc op x) =
      (\ op => PPrefixOp fc op x) <$> traverse (traverseOp @{Functor.CORE} cleanKindedName) op
    cleanNode (PSectionL fc op x) =
      (\ op => PSectionL fc op x) <$> traverse (traverseOp @{Functor.CORE} cleanKindedName) op
    cleanNode (PSectionR fc x op) =
      PSectionR fc x <$> traverse (traverseOp @{Functor.CORE} cleanKindedName) op
    cleanNode (PPi fc rig vis (Just n) arg ret) =
      (\ n => PPi fc rig vis n arg ret) <$> (cleanBinderName vis n)
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
