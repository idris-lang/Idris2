module Idris.Desugar

import Core.Context
import Core.Context.Log
import Core.CompileExpr
import Core.Core
import Core.Env
import Core.Metadata
import Core.Options
import Core.TT
import Core.Unify

import Libraries.Data.List.Extra
import Libraries.Data.StringMap
import Libraries.Data.ANameMap
import Libraries.Data.SortedMap

import Idris.Doc.String
import Idris.Error
import Idris.Pretty
import Idris.REPL.Opts
import Idris.Syntax
import Idris.Syntax.Builtin

import Idris.Elab.Implementation
import Idris.Elab.Interface

import Idris.Desugar.Mutual

import Parser.Lexer.Source
import Parser.Support

import TTImp.BindImplicits
import TTImp.Parser
import TTImp.ProcessType
import TTImp.TTImp
import TTImp.Utils

import Libraries.Data.IMaybe
import Libraries.Data.WithDefault
import Libraries.Utils.Shunting
import Libraries.Text.PrettyPrint.Prettyprinter

import Data.Maybe
import Data.List
import Data.List.Views
import Data.String

-- Convert high level Idris declarations (PDecl from Idris.Syntax) into
-- TTImp, recording any high level syntax info on the way (e.g. infix
-- operators)

-- Desugaring from high level Idris syntax to TTImp involves:

-- * Shunting infix operators into function applications according to precedence
-- * Replacing 'do' notating with applications of (>>=)
-- * Replacing string interpolation with concatenation by (++)
-- * Replacing pattern matching binds with 'case'
-- * Changing tuples to 'Pair/MkPair'
-- * List notation
-- * Replacing !-notation
-- * Dependent pair notation
-- * Idiom brackets

%default covering

public export
data Side = LHS | AnyExpr

export
Eq Side where
  LHS == LHS = True
  AnyExpr == AnyExpr = True
  _ == _ = False

export
extendSyn : {auto s : Ref Syn SyntaxInfo} ->
            {auto c : Ref Ctxt Defs} ->
            SyntaxInfo -> Core ()
extendSyn newsyn
    = do syn <- get Syn
         log "doc.module" 20 $ unlines
           [ "Old (" ++ unwords (map show $ saveMod syn) ++ "): "
              ++ show (modDocstrings syn)
           , "New (" ++ unwords (map show $ saveMod newsyn) ++ "): "
              ++ show (modDocstrings newsyn)
           ]

         -- Before we merge the two syntax environement, we remove the
         -- private fixities from the one we are importing.
         -- We keep the local private fixities since they are visible in the
         -- current file.
         let filteredFixities = removePrivate (fixities newsyn)
         put Syn ({ fixities $= merge filteredFixities,
                    ifaces $= merge (ifaces newsyn),
                    modDocstrings $= mergeLeft (modDocstrings newsyn),
                    modDocexports $= mergeLeft (modDocexports newsyn),
                    defDocstrings $= merge (defDocstrings newsyn),
                    bracketholes $= sortedNub . ((bracketholes newsyn) ++) }
                  syn)
  where
    removePrivate : ANameMap FixityInfo -> ANameMap FixityInfo
    removePrivate = fromList . filter ((/= Private) . vis . snd) . toList

mkPrec : Fixity -> Nat -> OpPrec
mkPrec InfixL = AssocL
mkPrec InfixR = AssocR
mkPrec Infix  = NonAssoc
mkPrec Prefix = Prefix

-- This is used to print the error message for fixities
[interpName] Interpolation ((OpStr' Name, FixityDeclarationInfo), b) where
  interpolate ((x, _), _) = show x.toName

[showWithLoc] Show ((OpStr' Name, FixityDeclarationInfo), b) where
  show ((x, DeclaredFixity y), _) = show x ++ " at " ++ show y.fc
  show ((x, UndeclaredFixity), _) = show x

-- Check that an operator does not have any conflicting fixities in scope.
-- Each operator can have its fixity defined multiple times across multiple
-- modules as long as the fixities are consistent. If they aren't, the fixity
-- can be hidden with %hide, this is handled by `removeFixity`.
-- Once conflicts are handled we return the operator precedence we found.
checkConflictingFixities : {auto s : Ref Syn SyntaxInfo} ->
                           {auto c : Ref Ctxt Defs} ->
                           (isPrefix : Bool) ->
                           WithFC (OpStr' Name) -> Core (OpPrec, FixityDeclarationInfo)
checkConflictingFixities isPrefix opn
  = do let op = nameRoot opn.val.toName
       foundFixities <- getFixityInfo op
       let (pre, inf) = partition ((== Prefix) . fix . snd) foundFixities
       case (isPrefix, pre, inf) of
            -- If we do not find any fixity, and it is a backticked operator, then we
            -- return the default fixity and associativity for backticked operators
            -- Otherwise, it's an unknown operator.
            (_, [], []) => case opn.val of
                              OpSymbols _ => throw (GenericMsg opn.fc "Unknown operator '\{op}'")
                              Backticked _ =>  pure (NonAssoc 1, UndeclaredFixity) -- Backticks are non associative by default

            (True, ((fxName, fx) :: _), _) => do
                -- in the prefix case, remove conflicts with infix (-)
                let extraFixities = pre ++ (filter (\(nm, _) => not $ nameRoot nm == "-") inf)
                unless (isCompatible fx extraFixities) $ warnConflict fxName extraFixities
                pure (mkPrec fx.fix fx.precedence, DeclaredFixity fx)
            -- Could not find any prefix operator fixities, there may still be conflicts with
            -- the infix ones.
            (True, [] , _) => throw (GenericMsg opn.fc $ "'\{op}' is not a prefix operator")

            (False, _, ((fxName, fx) :: _)) => do
                -- In the infix case, remove conflicts with prefix (-)
                let extraFixities = (filter (\(nm, _) => not $ nm == UN (Basic "-")) pre) ++ inf
                unless (isCompatible fx extraFixities) $ warnConflict fxName extraFixities
                pure (mkPrec fx.fix fx.precedence, DeclaredFixity fx)
            -- Could not find any infix operator fixities, there may be prefix ones
            (False, _, []) => throw (GenericMsg opn.fc $ "'\{op}' is not an infix operator")
  where
    -- Fixities are compatible with all others of the same name that share the same
    -- fixity, precedence, and binding information
    isCompatible :  FixityInfo -> (fixities : List (Name, FixityInfo)) -> Bool
    isCompatible fx
      = all (\fx' => fx.fix == fx'.fix
                  && fx.precedence == fx'.precedence
                  && fx.bindingInfo == fx'.bindingInfo) . map snd

    -- Emits a warning using the fixity that we picked and the list of all conflicting fixities
    warnConflict : (picked : Name) -> (conflicts : List (Name, FixityInfo)) -> Core ()
    warnConflict fxName all =
      recordWarning $ GenericWarn opn.fc $ """
                   operator fixity is ambiguous, we are picking \{show fxName} out of :
                   \{unlines $ map (\(nm, fx) => " - \{show nm}, precedence level \{show fx.precedence}") $ toList all}
                   To remove this warning, use `%hide` with the fixity to remove
                   For example: %hide \{show fxName}
                   """

checkConflictingBinding : Ref Ctxt Defs =>
                          Ref Syn SyntaxInfo =>
                          WithFC OpStr -> (foundFixity : FixityDeclarationInfo) ->
                          (usage : OperatorLHSInfo PTerm) -> (rhs : PTerm) -> Core ()
checkConflictingBinding opName foundFixity use_site rhs
    = if isCompatible foundFixity use_site
         then pure ()
         else throw $ OperatorBindingMismatch
             {print = byShow} opName.fc foundFixity use_site (opNameToEither opName.val) rhs !candidates
    where

      isCompatible : FixityDeclarationInfo -> OperatorLHSInfo PTerm -> Bool
      isCompatible UndeclaredFixity (NoBinder lhs) = True
      isCompatible UndeclaredFixity _ = False
      isCompatible (DeclaredFixity fixInfo) (NoBinder lhs) = fixInfo.bindingInfo == NotBinding
      isCompatible (DeclaredFixity fixInfo) (BindType name ty) = fixInfo.bindingInfo == Typebind
      isCompatible (DeclaredFixity fixInfo) (BindExpr name expr) = fixInfo.bindingInfo == Autobind
      isCompatible (DeclaredFixity fixInfo) (BindExplicitType name type expr)
          = fixInfo.bindingInfo == Autobind

      keepCompatibleBinding : BindingModifier -> (Name, GlobalDef) -> Core Bool
      keepCompatibleBinding compatibleBinder (name, def) = do
        fixities <- getFixityInfo (nameRoot name)
        let compatible = any (\(_, fx) => fx.bindingInfo == use_site.getBinder) fixities
        pure compatible

      candidates : Core (List String)
      candidates = do let DeclaredFixity fxInfo = foundFixity
                        | _ => pure [] -- if there is no declared fixity we can't know what's
                                       -- supposed to go there.
                      Just (nm, cs) <- getSimilarNames {keepPredicate = Just (keepCompatibleBinding fxInfo.bindingInfo)} opName.val.toName
                        | Nothing => pure []
                      ns <- currentNS <$> get Ctxt
                      pure (showSimilarNames ns opName.val.toName nm cs)

checkValidFixity : BindingModifier -> Fixity -> Nat -> Bool

-- If the fixity declaration is not binding, there are no restrictions
checkValidFixity NotBinding _ _ = True

-- If the fixity declaration is not binding, either typebind or autobind
-- the fixity can only be `infixr` with precedence `0`. We might want
-- to revisit that in the future, but as of right now we want to be
-- conservative and avoid abuse.
-- having multiple precedence levels would mean that if
-- =@ has higher precedence than -@
-- the expression (x : a) =@ b -@ (y : List a) =@ List b
-- would be bracketed as ((x : a) =@ b) -@ (y : List a) =@ List b
-- instead of (x : a) =@ (b -@ ((y : List a) =@ List b))
checkValidFixity _ InfixR 0 = True

-- If it's binding but not infixr precedence 0, raise an error
checkValidFixity _ _ _ = False

parameters (side : Side)
  toTokList : {auto s : Ref Syn SyntaxInfo} ->
              {auto c : Ref Ctxt Defs} ->
              PTerm -> Core (List (Tok ((OpStr, FixityDeclarationInfo), Maybe (OperatorLHSInfo PTerm)) PTerm))
  toTokList (POp fc (MkWithData _ l) opn r)
      = do (precInfo, fixInfo) <- checkConflictingFixities False opn
           unless (side == LHS) -- do not check for conflicting fixity on the LHS
                                -- This is because we do not parse binders on the lhs
                                -- and so, if we check, we will find uses of regular
                                -- operator when binding is expected.
                  (checkConflictingBinding opn fixInfo l r)
           rtoks <- toTokList r
           pure (Expr l.getLhs :: Op fc opn.fc ((opn.val, fixInfo), Just l) precInfo :: rtoks)
  toTokList (PPrefixOp fc opn arg)
      = do (precInfo, fixInfo) <- checkConflictingFixities True opn
           rtoks <- toTokList arg
           pure (Op fc opn.fc ((opn.val, fixInfo), Nothing) precInfo :: rtoks)
  toTokList t = pure [Expr t]

record BangData where
  constructor MkBangData
  nextName : Int
  bangNames : List (Name, FC, RawImp)
  mbNamespace : Maybe Namespace

initBangs : Maybe Namespace -> BangData
initBangs = MkBangData 0 []

addNS : Maybe Namespace -> Name -> Name
addNS (Just ns) n@(NS {}) = n
addNS (Just ns) n = NS ns n
addNS _ n = n

bindFun : FC -> Maybe Namespace -> RawImp -> RawImp -> RawImp
bindFun fc ns ma f =
  let fc = virtualiseFC fc in
  IApp fc (IApp fc (IVar fc (addNS ns $ UN $ Basic ">>=")) ma) f

seqFun : FC -> Maybe Namespace -> RawImp -> RawImp -> RawImp
seqFun fc ns ma mb =
  let fc = virtualiseFC fc in
  IApp fc (IApp fc (IVar fc (addNS ns (UN $ Basic ">>"))) ma) mb

bindBangs : List (Name, FC, RawImp) -> Maybe Namespace -> RawImp -> RawImp
bindBangs [] ns tm = tm
bindBangs ((n, fc, btm) :: bs) ns tm
    = bindBangs bs ns
    $ bindFun fc ns btm
    $ ILam EmptyFC top Explicit (Just n) (Implicit fc False) tm

idiomise : FC -> Maybe Namespace -> Maybe Namespace -> RawImp -> RawImp
idiomise fc dons mns (IAlternative afc u alts)
  = IAlternative afc (mapAltType (idiomise afc dons mns) u) (idiomise afc dons mns <$> alts)
idiomise fc dons mns (IApp afc f a)
  = let fc  = virtualiseFC fc
        app = UN $ Basic "<*>"
        nm  = maybe app (`NS` app) (mns <|> dons)
     in IApp fc (IApp fc (IVar fc nm) (idiomise afc dons mns f)) a
idiomise fc dons mns fn
  = let fc  = virtualiseFC fc
        pur = UN $ Basic "pure"
        nm  = maybe pur (`NS` pur) (mns <|> dons)
     in IApp fc (IVar fc nm) fn

data Bang : Type where

mutual
  desugarB : {auto s : Ref Syn SyntaxInfo} ->
             {auto b : Ref Bang BangData} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto o : Ref ROpts REPLOpts} ->
             Side -> List Name -> PTerm -> Core RawImp
  desugarB side ps (PRef fc x) = do
    let ns = mbNamespace !(get Bang)
    let pur = UN $ Basic "pure"
    case x == pur of -- implicitly add namespace to unqualified occurrences of `pure` in a qualified do-block
      False => pure $ IVar fc x
      True => pure $ IVar fc (maybe pur (`NS` pur) ns)

  -- Desugaring forall n1, n2, n3 . s into
  -- {0 n1 : ?} -> {0 n2 : ?} -> {0 n3 : ?} -> s
  desugarB side ps (Forall (MkWithData _ (names, scope)))
        = desugarForallNames ps (forget names)
      where
        desugarForallNames : (ctx : List Name) ->
                             (names : List (WithFC Name)) -> Core RawImp
        desugarForallNames ctx [] = desugarB side ctx scope
        desugarForallNames ctx (x :: xs)
          = IPi x.fc erased Implicit (Just x.val)
          <$> desugarB side ps (PImplicit x.fc)
          <*> desugarForallNames (x.val :: ctx) xs

  -- Desugaring (n1, n2, n3 : t) -> s into
  -- (n1 : t) -> (n2 : t) -> (n3 : t) -> s
  desugarB side ps
      (NewPi binder@(MkWithData _
          (MkPBinderScope (MkPBinder info (MkBasicMultiBinder rig names type)) scope)))
        = desugarMultiBinder ps (forget names)
      where
        desugarMultiBinder : (ctx : List Name) -> List (WithFC Name) -> Core RawImp
        desugarMultiBinder ctx []
          = desugarB side ctx scope
        desugarMultiBinder ctx (name :: xs)
          = let extendedCtx = name.val :: ps
            in IPi binder.fc rig
              <$> mapDesugarPiInfo extendedCtx info
              <*> (pure (Just name.val))
              <*> desugarB side ps type
              <*> desugarMultiBinder extendedCtx xs

  desugarB side ps (PPi fc rig p mn argTy retTy)
      = let ps' = maybe ps (:: ps) mn in
            pure $ IPi fc rig !(traverse (desugar side ps') p)
                              mn !(desugarB side ps argTy)
                                 !(desugarB side ps' retTy)
  desugarB side ps (PLam fc rig p pat@(PRef prefFC n@(UN nm)) argTy scope)
      =  if isPatternVariable nm
           then do whenJust (isConcreteFC prefFC) $ \nfc
                     => addSemanticDecorations [(nfc, Bound, Just n)]
                   pure $ ILam fc rig !(traverse (desugar AnyExpr ps) p)
                           (Just n) !(desugarB AnyExpr ps argTy)
                                    !(desugar AnyExpr (n :: ps) scope)
           else pure $ ILam EmptyFC rig !(traverse (desugar AnyExpr ps) p)
                   (Just (MN "lamc" 0)) !(desugarB AnyExpr ps argTy) $
                 ICase fc [] (IVar EmptyFC (MN "lamc" 0)) (Implicit fc False)
                     [snd !(desugarClause ps True (MkPatClause fc pat scope []))]
  desugarB side ps (PLam fc rig p (PRef _ n@(MN {})) argTy scope)
      = pure $ ILam fc rig !(traverse (desugar AnyExpr ps) p)
                           (Just n) !(desugarB AnyExpr ps argTy)
                                    !(desugar AnyExpr (n :: ps) scope)
  desugarB side ps (PLam fc rig p (PImplicit _) argTy scope)
      = pure $ ILam fc rig !(traverse (desugar AnyExpr ps) p)
                           Nothing !(desugarB AnyExpr ps argTy)
                                   !(desugar AnyExpr ps scope)
  desugarB side ps (PLam fc rig p pat argTy scope)
      = pure $ ILam EmptyFC rig !(traverse (desugar AnyExpr ps) p)
                   (Just (MN "lamc" 0)) !(desugarB AnyExpr ps argTy) $
                 ICase fc [] (IVar EmptyFC (MN "lamc" 0)) (Implicit fc False)
                     [snd !(desugarClause ps True (MkPatClause fc pat scope []))]
  desugarB side ps (PLet fc rig (PRef prefFC n) nTy nVal scope [])
      = do whenJust (isConcreteFC prefFC) $ \nfc =>
             addSemanticDecorations [(nfc, Bound, Just n)]
           pure $ ILet fc prefFC rig n !(desugarB side ps nTy) !(desugarB side ps nVal)
                                       !(desugar side (n :: ps) scope)
  desugarB side ps (PLet fc rig pat nTy nVal scope alts)
      = pure $ ICase fc [] !(desugarB side ps nVal) !(desugarB side ps nTy)
                        !(traverse (map snd . desugarClause ps True)
                            (MkPatClause fc pat scope [] :: alts))
  desugarB side ps (PCase fc opts scr cls)
      = do opts <- traverse (desugarFnOpt ps) opts
           scr <- desugarB side ps scr
           let scrty = Implicit (virtualiseFC fc) False
           cls <- traverse (map snd . desugarClause ps True) cls
           pure $ ICase fc opts scr scrty cls
  desugarB side ps (PLocal fc xs scope)
      = let ps' = definedIn (map val xs) ++ ps in
            pure $ ILocal fc (concat !(traverse (desugarDecl ps') xs))
                             !(desugar side ps' scope)
  desugarB side ps (PApp pfc (PUpdate fc fs) rec)
      = pure $ IUpdate pfc !(traverse (desugarUpdate side ps) fs)
                           !(desugarB side ps rec)
  desugarB side ps (PUpdate fc fs)
      = desugarB side ps
      $ let vfc = virtualiseFC fc in
      PLam vfc top Explicit (PRef vfc (MN "rec" 0)) (PImplicit vfc)
      $ PApp vfc (PUpdate fc fs) (PRef vfc (MN "rec" 0))
  desugarB side ps (PApp fc x y)
      = pure $ IApp fc !(desugarB side ps x) !(desugarB side ps y)
  desugarB side ps (PAutoApp fc x y)
      = pure $ IAutoApp fc !(desugarB side ps x) !(desugarB side ps y)
  desugarB side ps (PWithApp fc x y)
      = pure $ IWithApp fc !(desugarB side ps x) !(desugarB side ps y)
  desugarB side ps (PNamedApp fc x argn y)
      = pure $ INamedApp fc !(desugarB side ps x) argn !(desugarB side ps y)
  desugarB side ps (PDelayed fc r ty)
      = pure $ IDelayed fc r !(desugarB side ps ty)
  desugarB side ps (PDelay fc tm)
      = pure $ IDelay fc !(desugarB side ps tm)
  desugarB side ps (PForce fc tm)
      = pure $ IForce fc !(desugarB side ps tm)
  desugarB side ps (PEq fc l r)
      = do l' <- desugarB side ps l
           r' <- desugarB side ps r
           pure $ IAlternative fc FirstSuccess
                     [apply (IVar fc (UN $ Basic "===")) [l', r'],
                      apply (IVar fc (UN $ Basic "~=~")) [l', r']]
  desugarB side ps (PBracketed fc e) = desugarB side ps e
  desugarB side ps (POp fc l op r)
      = do ts <- toTokList side (POp fc l op r)
           tree <- parseOps @{interpName} @{showWithLoc} ts
           unop <- desugarTree side ps (mapFst (\((x, _), y) => (x, y)) tree)
           desugarB side ps unop
  desugarB side ps (PPrefixOp fc op arg)
      = do ts <- toTokList side (PPrefixOp fc op arg)
           tree <- parseOps @{interpName} @{showWithLoc} ts
           unop <- desugarTree side ps (mapFst (\((x, _), y) => (x, y)) tree)
           desugarB side ps unop
  desugarB side ps (PSectionL fc op arg)
      = do syn <- get Syn
           -- It might actually be a prefix argument rather than a section
           -- so check that first, otherwise desugar as a lambda
           case lookupName op.val.toName (prefixes syn) of
                [] =>
                    desugarB side ps
                        (PLam fc top Explicit (PRef fc (MN "arg" 0)) (PImplicit fc)
                            (POp fc (MkFCVal op.fc (NoBinder (PRef fc (MN "arg" 0)))) op arg))
                (prec :: _) => desugarB side ps (PPrefixOp fc op arg)
  desugarB side ps (PSectionR fc arg op)
      = desugarB side ps
          (PLam fc top Explicit (PRef fc (MN "arg" 0)) (PImplicit fc)
              (POp fc (MkFCVal op.fc $ NoBinder arg) op (PRef fc (MN "arg" 0))))
  desugarB side ps (PSearch fc depth) = pure $ ISearch fc depth
  desugarB side ps (PPrimVal fc (BI x))
      = case !fromIntegerName of
             Nothing =>
                pure $ IAlternative fc (UniqueDefault (IPrimVal fc (BI x)))
                                [IPrimVal fc (BI x),
                                 IPrimVal fc (I (fromInteger x))]
             Just fi =>
               let vfc = virtualiseFC fc in
               pure $ IApp vfc (IVar vfc fi) (IPrimVal fc (BI x))
  desugarB side ps (PPrimVal fc (Ch x))
      = case !fromCharName of
             Nothing =>
                pure $ IPrimVal fc (Ch x)
             Just f =>
               let vfc = virtualiseFC fc in
               pure $ IApp vfc (IVar vfc f) (IPrimVal fc (Ch x))
  desugarB side ps (PPrimVal fc (Db x))
      = case !fromDoubleName of
             Nothing =>
                pure $ IPrimVal fc (Db x)
             Just f =>
               let vfc = virtualiseFC fc in
               pure $ IApp vfc (IVar vfc f) (IPrimVal fc (Db x))
  desugarB side ps (PPrimVal fc x) = pure $ IPrimVal fc x
  desugarB side ps (PQuote fc tm)
      = do let q = IQuote fc !(desugarB side ps tm)
           case side of
                AnyExpr => pure $ maybeIApp fc !fromTTImpName q
                _ => pure q
  desugarB side ps (PQuoteName fc n)
      = do let q = IQuoteName fc n
           case side of
                AnyExpr => pure $ maybeIApp fc !fromNameName q
                _ => pure q
  desugarB side ps (PQuoteDecl fc x)
      = do xs <- traverse (desugarDecl ps) x
           let dls = IQuoteDecl fc (concat xs)
           case side of
                AnyExpr => pure $ maybeIApp fc !fromDeclsName dls
                _ => pure dls
  desugarB side ps (PUnquote fc tm)
      = pure $ IUnquote fc !(desugarB side ps tm)
  desugarB side ps (PRunElab fc tm)
      = pure $ IRunElab fc True !(desugarB side ps tm)
  desugarB side ps (PHole fc br holename)
      = do when br $ update Syn { bracketholes $= ((UN (Basic holename)) ::) }
           pure $ IHole fc holename
  desugarB side ps (PType fc) = pure $ IType fc
  desugarB side ps (PAs fc nameFC vname pattern)
      = pure $ IAs fc nameFC UseRight vname !(desugarB side ps pattern)
  desugarB side ps (PDotted fc x)
      = pure $ IMustUnify fc UserDotted !(desugarB side ps x)
  desugarB side ps (PImplicit fc) = pure $ Implicit fc True
  desugarB side ps (PInfer fc)
    = do when (side == LHS) $
           throw (GenericMsg fc "? is not a valid pattern")
         pure $ Implicit fc False
  desugarB side ps (PMultiline fc hashtag indent lines)
      = pure $ maybeIApp fc !fromStringName !(expandString side ps fc hashtag !(trimMultiline fc indent lines))

  -- We only add `fromString` if we are looking at a plain string literal.
  -- Interpolated string literals don't have a `fromString` call since they
  -- are always concatenated with other strings and therefore can never use
  -- another `fromString` implementation that differs from `id`.
  desugarB side ps (PString fc hashtag [])
      = pure $ maybeIApp fc !fromStringName (IPrimVal fc (Str ""))
  desugarB side ps (PString fc hashtag [StrLiteral fc' str])
      = case unescape hashtag str of
             Just str => pure $ maybeIApp fc !fromStringName (IPrimVal fc' (Str str))
             Nothing => throw (GenericMsg fc "Invalid escape sequence: \{show str}")
  desugarB side ps (PString fc hashtag strs)
      = expandString side ps fc hashtag strs

  desugarB side ps (PDoBlock fc ns block)
      = expandDo side ps fc ns block
  desugarB side ps (PBang fc term)
      = do itm <- desugarB side ps term
           bs <- get Bang
           let bn = MN "bind" (nextName bs)
           put Bang ({ nextName $= (+1),
                       bangNames $= ((bn, fc, itm) ::)
                     } bs)
           pure (IVar (virtualiseFC fc) bn)
  desugarB side ps (PIdiom fc ns term)
      = do itm <- desugarB side ps term
           logRaw "desugar.idiom" 10 "Desugaring idiom for" itm
           let val = idiomise fc (mbNamespace !(get Bang)) ns itm
           logRaw "desugar.idiom" 10 "Desugared to" val
           pure val
  desugarB side ps (PList fc nilFC args)
      = expandList side ps nilFC args
  desugarB side ps (PSnocList fc nilFC args)
      = expandSnocList side ps nilFC args
  desugarB side ps (PPair fc l r)
      = do l' <- desugarB side ps l
           r' <- desugarB side ps r
           let pval = apply (IVar fc mkpairname) [l', r']
           pure $ IAlternative fc (UniqueDefault pval)
                  [apply (IVar fc pairname) [l', r'], pval]
  desugarB side ps (PDPair fc opFC (PRef nameFC n@(UN _)) (PImplicit _) r)
      = do r' <- desugarB side ps r
           let pval = apply (IVar opFC mkdpairname) [IVar nameFC n, r']
           let vfc = virtualiseFC nameFC
           whenJust (isConcreteFC nameFC) $ \nfc =>
             addSemanticDefault (nfc, Bound, Just n)
           pure $ IAlternative fc (UniqueDefault pval)
                  [apply (IVar opFC dpairname)
                      [Implicit vfc False,
                       ILam nameFC top Explicit (Just n) (Implicit vfc False) r'],
                   pval]
  desugarB side ps (PDPair fc opFC (PRef namefc n@(UN _)) ty r)
      = do ty' <- desugarB side ps ty
           r' <- desugarB side ps r
           pure $ apply (IVar opFC dpairname)
                        [ty', ILam namefc top Explicit (Just n) ty' r']
  desugarB side ps (PDPair fc opFC l (PImplicit _) r)
      = do l' <- desugarB side ps l
           r' <- desugarB side ps r
           pure $ apply (IVar opFC mkdpairname) [l', r']
  desugarB side ps (PDPair fc opFC l ty r)
      = throw (GenericMsg fc "Invalid dependent pair type")
  desugarB side ps (PUnit fc)
      = pure $ IAlternative fc (UniqueDefault (IVar fc (UN $ Basic "MkUnit")))
               [IVar fc (UN $ Basic "Unit"),
                IVar fc (UN $ Basic "MkUnit")]
  desugarB side ps (PIfThenElse fc x t e)
      = let fc = virtualiseFC fc in
        pure $ ICase fc [] !(desugarB side ps x) (IVar fc (UN $ Basic "Bool"))
                   [PatClause fc (IVar fc (UN $ Basic "True")) !(desugar side ps t),
                    PatClause fc (IVar fc (UN $ Basic "False")) !(desugar side ps e)]
  desugarB side ps (PComprehension fc ret conds) = do
        let ns = mbNamespace !(get Bang)
        desugarB side ps (PDoBlock fc ns (map (guard ns) conds ++ [toPure ns ret]))
    where
      guard : Maybe Namespace -> PDo -> PDo
      guard ns (DoExp fc tm)
       = DoExp fc (PApp fc (PRef fc (mbApplyNS ns $ UN $ Basic "guard")) tm)
      guard ns d = d

      toPure : Maybe Namespace -> PTerm -> PDo
      toPure ns tm = DoExp fc (PApp fc (PRef fc (mbApplyNS ns $ UN $ Basic "pure")) tm)
  desugarB side ps (PRewrite fc rule tm)
      = pure $ IRewrite fc !(desugarB side ps rule) !(desugarB side ps tm)
  desugarB side ps (PRange fc start next end)
      = let fc = virtualiseFC fc in
        desugarB side ps $ case next of
           Nothing => papply fc (PRef fc (UN $ Basic "rangeFromTo")) [start,end]
           Just n  => papply fc (PRef fc (UN $ Basic "rangeFromThenTo")) [start, n, end]
  desugarB side ps (PRangeStream fc start next)
      = let fc = virtualiseFC fc in
        desugarB side ps $ case next of
           Nothing => papply fc (PRef fc (UN $ Basic "rangeFrom")) [start]
           Just n  => papply fc (PRef fc (UN $ Basic "rangeFromThen")) [start, n]
  desugarB side ps (PUnifyLog fc lvl tm)
      = pure $ IUnifyLog fc lvl !(desugarB side ps tm)
  desugarB side ps (PPostfixApp fc rec projs)
      = desugarB side ps
      $ foldl (\x, (fc, proj) => PApp fc (PRef fc proj) x) rec projs
  desugarB side ps (PPostfixAppPartial fc projs)
      = do let vfc = virtualiseFC fc
           let var = PRef vfc (MN "paRoot" 0)
           desugarB side ps $
             PLam fc top Explicit var (PImplicit vfc) $
               foldl (\r, (fc, proj) => PApp fc (PRef fc proj) r) var projs
  desugarB side ps (PWithUnambigNames fc ns rhs)
      = IWithUnambigNames fc ns <$> desugarB side ps rhs

  desugarUpdate : {auto s : Ref Syn SyntaxInfo} ->
                  {auto b : Ref Bang BangData} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  {auto m : Ref MD Metadata} ->
                  {auto o : Ref ROpts REPLOpts} ->
                  Side -> List Name -> PFieldUpdate -> Core IFieldUpdate
  desugarUpdate side ps (PSetField p v)
      = pure (ISetField p !(desugarB side ps v))
  desugarUpdate side ps (PSetFieldApp p v)
      = pure (ISetFieldApp p !(desugarB side ps v))

  expandList : {auto s : Ref Syn SyntaxInfo} ->
               {auto b : Ref Bang BangData} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto m : Ref MD Metadata} ->
               {auto o : Ref ROpts REPLOpts} ->
               Side -> List Name ->
               (nilFC : FC) -> List (FC, PTerm) -> Core RawImp
  expandList side ps nilFC [] = pure (IVar nilFC (UN $ Basic "Nil"))
  expandList side ps nilFC ((consFC, x) :: xs)
      = pure $ apply (IVar consFC (UN $ Basic "::"))
                [!(desugarB side ps x), !(expandList side ps nilFC xs)]

  expandSnocList
             : {auto s : Ref Syn SyntaxInfo} ->
               {auto b : Ref Bang BangData} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto m : Ref MD Metadata} ->
               {auto o : Ref ROpts REPLOpts} ->
               Side -> List Name -> (nilFC : FC) ->
               SnocList (FC, PTerm) -> Core RawImp
  expandSnocList side ps nilFC [<] = pure (IVar nilFC (UN $ Basic "Lin"))
  expandSnocList side ps nilFC (xs :< (consFC, x))
      = pure $ apply (IVar consFC (UN $ Basic ":<"))
                [!(expandSnocList side ps nilFC xs) , !(desugarB side ps x)]

  maybeIApp : FC -> Maybe Name -> RawImp -> RawImp
  maybeIApp fc nm tm
      = case nm of
             Nothing => tm
             Just f =>
               let fc = virtualiseFC fc in
               IApp fc (IVar fc f) tm

  expandString : {auto s : Ref Syn SyntaxInfo} ->
                 {auto b : Ref Bang BangData} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 Side -> List Name -> FC -> Nat -> List PStr -> Core RawImp
  expandString side ps fc hashtag xs
    = do xs <- traverse toRawImp (filter notEmpty $ mergeStrLit xs)
         pure $ case xs of
           [] => IPrimVal fc (Str "")
           (_ :: _) =>
             let vfc = virtualiseFC fc in
             IApp vfc
               (INamedApp vfc
                 (IVar vfc (NS preludeNS $ UN $ Basic "concat"))
                 (UN $ Basic "t")
                 (IVar vfc (NS preludeNS $ UN $ Basic "List")))
               (strInterpolate xs)
    where
      toRawImp : PStr -> Core RawImp
      toRawImp (StrLiteral fc str) =
        case unescape hashtag str of
             Just str => pure $ IPrimVal fc (Str str)
             Nothing => throw (GenericMsg fc "Invalid escape sequence: \{show str}")
      toRawImp (StrInterp fc tm) = desugarB side ps tm

      -- merge neighbouring StrLiteral
      mergeStrLit : List PStr -> List PStr
      mergeStrLit xs = case List.spanBy isStrLiteral xs of
        ([], []) => []
        ([], x::xs) => x :: mergeStrLit xs
        (lits@(_::_), xs) =>
          -- TODO: merge all the FCs of the merged literals!
          let fc  = fst $ head lits in
          let lit = fastConcat $ snd <$> lits in
          StrLiteral fc lit :: mergeStrLit xs

      notEmpty : PStr -> Bool
      notEmpty (StrLiteral _ str) = str /= ""
      notEmpty (StrInterp {}) = True

      strInterpolate : List RawImp -> RawImp
      strInterpolate []
        = IVar EmptyFC nilName
      strInterpolate (x :: xs)
        = let xFC = virtualiseFC (getFC x) in
          apply (IVar xFC consName)
          [ IApp xFC (IVar EmptyFC interpolateName)
                     x
          , strInterpolate xs
          ]

  trimMultiline : FC -> Nat -> List (List PStr) -> Core (List PStr)
  trimMultiline fc indent lines
      = do lines <- trimLast fc lines
           lines <- traverse (trimLeft indent) lines
           pure $ concat $ dropLastNL lines

    where
      trimLast : FC -> List (List PStr) -> Core (List (List PStr))
      trimLast fc lines with (snocList lines)
        trimLast fc [] | Empty = throw $ BadMultiline fc "Expected new line"
        trimLast _ (initLines `snoc` []) | Snoc [] initLines _ = pure lines
        trimLast _ (initLines `snoc` [StrLiteral fc str]) | Snoc [(StrLiteral {})] initLines _
            = if any (not . isSpace) (fastUnpack str)
                     then throw $ BadMultiline fc "Closing delimiter of multiline strings cannot be preceded by non-whitespace characters"
                     else pure initLines
        trimLast _ (initLines `snoc` xs) | Snoc xs initLines _
            = let fc = fromMaybe fc $ findBy isStrInterp xs in
                  throw $ BadMultiline fc "Closing delimiter of multiline strings cannot be preceded by non-whitespace characters"

      trimLeft : Nat -> List PStr -> Core (List PStr)
      trimLeft indent [] = pure []
      trimLeft indent [StrLiteral fc str]
          = let (trimed, rest) = splitAt indent (fastUnpack str) in
            if any (not . isSpace) trimed
              then throw $ BadMultiline fc "Line is less indented than the closing delimiter"
              else let str = if null rest then "\n" else fastPack rest in
                   pure [StrLiteral fc str]
      trimLeft indent (StrLiteral fc str :: xs)
          = let (trimed, rest) = splitAt indent (fastUnpack str) in
            if any (not . isSpace) trimed || length trimed < indent
              then throw $ BadMultiline fc "Line is less indented than the closing delimiter"
             else pure $ (StrLiteral fc (fastPack rest))::xs
      trimLeft indent xs = throw $ BadMultiline fc "Line is less indented than the closing delimiter"

      mapLast : (a -> a) -> List a -> List a
      mapLast f [] = []
      mapLast f [x] = [f x]
      mapLast f (x :: xs) = x :: mapLast f xs

      dropLastNL : List (List PStr) -> List (List PStr)
      dropLastNL
          = mapLast $ mapLast $
              \case StrLiteral fc str => StrLiteral fc (fst $ break isNL str)
                    other => other

  expandDo : {auto s : Ref Syn SyntaxInfo} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {auto m : Ref MD Metadata} ->
             {auto o : Ref ROpts REPLOpts} ->
             Side -> List Name -> FC -> Maybe Namespace -> List PDo -> Core RawImp
  expandDo side ps fc ns [] = throw (GenericMsg fc "Do block cannot be empty")
  expandDo side ps _ ns [DoExp fc tm] = desugarDo side ps ns tm
  expandDo side ps fc ns [e]
      = throw (GenericMsg (getLoc e)
                  "Last statement in do block must be an expression")
  expandDo side ps topfc ns (DoExp fc tm :: rest)
      = do tm' <- desugarDo side ps ns tm
           rest' <- expandDo side ps topfc ns rest
           pure $ seqFun fc ns tm' rest'
  expandDo side ps topfc ns (DoBind fc nameFC n rig ty tm :: rest)
      = do tm' <- desugarDo side ps ns tm
           whenJust (isConcreteFC nameFC) $ \nfc => addSemanticDecorations [(nfc, Bound, Just n)]
           ty' <- maybe (pure $ Implicit (virtualiseFC fc) False)
                        (\ty => desugarDo side ps ns ty) ty
           rest' <- expandDo side ps topfc ns rest
           pure $ bindFun fc ns tm'
                $ ILam nameFC rig Explicit (Just n) ty' rest'
  expandDo side ps topfc ns (DoBindPat fc pat ty exp alts :: rest)
      = do pat' <- desugarDo LHS ps ns pat
           (newps, bpat) <- bindNames False pat'
           exp' <- desugarDo side ps ns exp
           alts' <- traverse (map snd . desugarClause ps True) alts
           let ps' = newps ++ ps
           let fcOriginal = fc
           let fc = virtualiseFC fc
           let patFC = virtualiseFC (getFC bpat)
           ty' <- maybe (pure $ Implicit fc False)
                        (\ty => desugarDo side ps ns ty) ty
           rest' <- expandDo side ps' topfc ns rest
           pure $ bindFun fc ns exp'
                $ ILam EmptyFC top Explicit (Just (MN "_" 0))
                          ty'
                          (ICase fc [] (IVar patFC (MN "_" 0))
                               (Implicit fc False)
                               (PatClause fcOriginal bpat rest'
                                  :: alts'))
  expandDo side ps topfc ns (DoLet fc lhsFC n rig ty tm :: rest)
      = do b <- newRef Bang (initBangs ns)
           tm' <- desugarB side ps tm
           ty' <- desugarDo side ps ns ty
           rest' <- expandDo side ps topfc ns rest
           whenJust (isConcreteFC lhsFC) $ \nfc =>
             addSemanticDecorations [(nfc, Bound, Just n)]
           let bind = ILet fc lhsFC rig n ty' tm' rest'
           bd <- get Bang
           pure $ bindBangs (bangNames bd) ns bind
  expandDo side ps topfc ns (DoLetPat fc pat ty tm alts :: rest)
      = do b <- newRef Bang (initBangs ns)
           pat' <- desugarDo LHS ps ns pat
           ty' <- desugarDo side ps ns ty
           (newps, bpat) <- bindNames False pat'
           tm' <- desugarB side ps tm
           alts' <- traverse (map snd . desugarClause ps True) alts
           let ps' = newps ++ ps
           rest' <- expandDo side ps' topfc ns rest
           bd <- get Bang
           let fc = virtualiseFC fc
           pure $ bindBangs (bangNames bd) ns $
                    ICase fc [] tm' ty'
                       (PatClause fc bpat rest'
                                  :: alts')
  expandDo side ps topfc ns (DoLetLocal fc decls :: rest)
      = do decls' <- traverse (desugarDecl ps) decls
           rest' <- expandDo side ps topfc ns rest
           pure $ ILocal fc (concat decls') rest'
  expandDo side ps topfc ns (DoRewrite fc rule :: rest)
      = do rule' <- desugarDo side ps ns rule
           rest' <- expandDo side ps topfc ns rest
           pure $ IRewrite fc rule' rest'

  -- Replace all operator by function application
  desugarTree : Side -> List Name -> Tree (OpStr, Maybe $ OperatorLHSInfo PTerm) PTerm ->
                Core PTerm
  desugarTree side ps (Infix loc eqFC (OpSymbols $ UN $ Basic "=", _) l r) -- special case since '=' is special syntax
      = pure $ PEq eqFC !(desugarTree side ps l) !(desugarTree side ps r)

  desugarTree side ps (Infix loc _ (OpSymbols $ UN $ Basic "$", _) l r) -- special case since '$' is special syntax
      = do l' <- desugarTree side ps l
           r' <- desugarTree side ps r
           pure (PApp loc l' r')
  -- normal operators
  desugarTree side ps (Infix loc opFC (op, Just (NoBinder lhs)) l r)
      = do l' <- desugarTree side ps l
           r' <- desugarTree side ps r
           pure (PApp loc (PApp loc (PRef opFC op.toName) l') r')
  -- (x : ty) =@ f x ==>> (=@) ty (\x : ty => f x)
  desugarTree side ps (Infix loc opFC (op, Just (BindType pat lhs)) l r)
      = do l' <- desugarTree side ps l
           body <- desugarTree side ps r
           pure $ PApp loc (PApp loc (PRef opFC op.toName) l')
                      (PLam loc top Explicit pat l' body)
  -- (x := exp) =@ f x ==>> (=@) exp (\x : ? => f x)
  desugarTree side ps (Infix loc opFC (op, Just (BindExpr pat lhs)) l r)
      = do l' <- desugarTree side ps l
           body <- desugarTree side ps r
           pure $ PApp loc (PApp loc (PRef opFC op.toName) l')
                      (PLam loc top Explicit pat (PInfer opFC) body)

  -- (x : ty := exp) =@ f x ==>> (=@) exp (\x : ty => f x)
  desugarTree side ps (Infix loc opFC (op, Just (BindExplicitType pat ty expr)) l r)
      = do l' <- desugarTree side ps l
           body <- desugarTree side ps r
           pure $ PApp loc (PApp loc (PRef opFC op.toName) l')
                      (PLam loc top Explicit pat ty body)
  desugarTree side ps (Infix loc opFC (op, Nothing) _ r)
      = throw $ InternalError "illegal fixity: Parsed as infix but no binding information"

  -- negation is a special case, since we can't have an operator with
  -- two meanings otherwise
  --
  -- Note: In case of negated signed integer literals, we apply the
  -- negation directly. Otherwise, the literal might be
  -- truncated to 0 before being passed on to `negate`.
  desugarTree side ps (Pre loc opFC (OpSymbols $ UN $ Basic "-", _) $ Leaf $ PPrimVal fc c)
    = let newFC    = fromMaybe EmptyFC (mergeFC loc fc)
          continue = desugarTree side ps . Leaf . PPrimVal newFC
       in case c of
            I   x => continue $ I (-x)
            I8  x => continue $ I8 (-x)
            I16 x => continue $ I16 (-x)
            I32 x => continue $ I32 (-x)
            I64 x => continue $ I64 (-x)
            BI  x => continue $ BI (-x)

            -- not a signed integer literal. proceed by desugaring
            -- and applying to `negate`.
            _     => do arg' <- desugarTree side ps (Leaf $ PPrimVal fc c)
                        pure (PApp loc (PRef opFC (UN $ Basic "negate")) arg')

  desugarTree side ps (Pre loc opFC (OpSymbols $ UN $ Basic "-", _) arg)
    = do arg' <- desugarTree side ps arg
         pure (PApp loc (PRef opFC (UN $ Basic "negate")) arg')

  desugarTree side ps (Pre loc opFC (op, _) arg)
      = do arg' <- desugarTree side ps arg
           pure (PApp loc (PRef opFC op.toName) arg')
  desugarTree side ps (Leaf t) = pure t

  desugarType : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto m : Ref MD Metadata} ->
                {auto o : Ref ROpts REPLOpts} ->
                List Name -> PTypeDecl -> Core (List ImpTy)
  desugarType ps pty@(MkWithData _ $ MkPTy names d ty)
      = flip Core.traverse (forget names) $ \(doc, n) : (String, WithFC Name) =>
          do addDocString n.val (d ++ doc)
             syn <- get Syn
             pure $ Mk [pty.fc, n] !(bindTypeNames pty.fc (usingImpl syn)
                                                 ps !(desugar AnyExpr ps ty))

  -- Attempt to get the function name from a function pattern. For example,
  --   - given the pattern 'f x y', getClauseFn would return 'f'.
  --   - given the pattern 'x == y', getClausefn would return '=='.
  getClauseFn : RawImp -> Core Name
  getClauseFn (IVar _ n) = pure n
  getClauseFn (IApp _ f _) = getClauseFn f
  getClauseFn (IWithApp _ f _) = getClauseFn f
  getClauseFn (IAutoApp _ f _) = getClauseFn f
  getClauseFn (INamedApp _ f _ _) = getClauseFn f
  getClauseFn tm = throw $ GenericMsg (getFC tm) "Head term in pattern must be a function name"

  desugarLHS : {auto s : Ref Syn SyntaxInfo} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto o : Ref ROpts REPLOpts} ->
               List Name -> (arg : Bool) -> PTerm ->
               Core (IMaybe (not arg) Name, List Name, RawImp)
                  -- ^ we only look for the head name of the expression...
                  --   if we are actually looking at a headed thing!
  desugarLHS ps arg lhs =
    do rawlhs <- desugar LHS ps lhs
       inm <- iunless arg $ getClauseFn rawlhs
       (bound, blhs) <- bindNames arg rawlhs
       log "desugar.lhs" 10 "Desugared \{show lhs} to \{show blhs}"
       iwhenJust inm $ \ nm =>
         when (nm `elem` bound) $ do
           let fc = getPTermLoc lhs
           throw $ GenericMsg fc $ concat $ the (List String)
             [ "Declaration name ("
             , show nm
             , ") shadowed by a pattern variable."
             ]

       pure (inm, bound, blhs)

  desugarWithProblem :
    {auto s : Ref Syn SyntaxInfo} ->
    {auto c : Ref Ctxt Defs} ->
    {auto u : Ref UST UState} ->
    {auto m : Ref MD Metadata} ->
    {auto o : Ref ROpts REPLOpts} ->
    List Name -> PWithProblem ->
    Core (RigCount, RawImp, Maybe (RigCount, Name))
  desugarWithProblem ps (MkPWithProblem rig wval mnm)
    = (rig,,mnm) <$> desugar AnyExpr ps wval

  desugarClause : {auto s : Ref Syn SyntaxInfo} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  {auto m : Ref MD Metadata} ->
                  {auto o : Ref ROpts REPLOpts} ->
                  List Name -> (arg : Bool) -> PClause ->
                  Core (IMaybe (not arg) Name, ImpClause)
  desugarClause ps arg (MkPatClause fc lhs rhs wheres)
      = do ws <- traverse (desugarDecl ps) wheres

           (nm, bound, lhs') <- desugarLHS ps arg lhs

           -- desugar rhs, putting where clauses as local definitions
           rhs' <- desugar AnyExpr (bound ++ ps) rhs
           let rhs' = case ws of
                        [] => rhs'
                        _ => ILocal fc (concat ws) rhs'

           pure (nm, PatClause fc lhs' rhs')

  desugarClause ps arg (MkWithClause fc lhs wps flags cs)
      = do cs' <- traverse (map snd . desugarClause ps arg) cs
           (nm, bound, lhs') <- desugarLHS ps arg lhs
           wps' <- traverseList1 (desugarWithProblem (bound ++ ps)) wps
           pure (nm, mkWithClause fc lhs' wps' flags cs')

  desugarClause ps arg (MkImpossible fc lhs)
      = do (nm, _, lhs') <- desugarLHS ps arg lhs
           pure (nm, ImpossibleClause fc lhs')

  desugarData : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto m : Ref MD Metadata} ->
                {auto o : Ref ROpts REPLOpts} ->
                List Name -> (doc : String) ->
                PDataDecl -> Core ImpData
  desugarData ps doc (MkPData fc n tycon opts datacons)
      = do addDocString n doc
           syn <- get Syn
           mm <- traverse (desugarType ps) datacons
           pure $ MkImpData fc n
                   !(flip traverseOpt tycon $ \ tycon => do
                      tycon <- desugar AnyExpr ps tycon
                      bindTypeNames fc (usingImpl syn) ps tycon)
                   opts
                   (concat mm)
  desugarData ps doc (MkPLater fc n tycon)
      = do addDocString n doc
           syn <- get Syn
           pure $ MkImpLater fc n !(bindTypeNames fc (usingImpl syn)
                                                  ps !(desugar AnyExpr ps tycon))

  desugarField : {auto s : Ref Syn SyntaxInfo} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 {auto m : Ref MD Metadata} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 List Name -> Namespace -> PField ->
                 Core (List IField)
  desugarField ps ns field
      = flip Core.traverse field.names $ \n : WithFC Name => do
           addDocStringNS ns n.val field.doc
           addDocStringNS ns (toRF n.val) field.doc
           syn <- get Syn
           p' <- traverse (desugar AnyExpr ps) field.val.info
           ty' <- bindTypeNames field.fc (usingImpl syn) ps !(desugar AnyExpr ps field.val.boundType)
           pure (Mk [field.fc, field.rig, n] (MkPiBindData p' ty'))

        where
          toRF : Name -> Name
          toRF (UN (Basic n)) = UN (Field n)
          toRF n = n

  export
  desugarFnOpt : {auto s : Ref Syn SyntaxInfo} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 {auto m : Ref MD Metadata} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 List Name -> PFnOpt -> Core FnOpt
  desugarFnOpt ps (IFnOpt f) = pure f
  desugarFnOpt ps (PForeign tms)
      = do tms' <- traverse (desugar AnyExpr ps) tms
           pure (ForeignFn tms')
  desugarFnOpt ps (PForeignExport tms)
      = do tms' <- traverse (desugar AnyExpr ps) tms
           pure (ForeignExport tms')

  %inline
  mapDesugarPiInfo : {auto s : Ref Syn SyntaxInfo} ->
                     {auto c : Ref Ctxt Defs} ->
                     {auto u : Ref UST UState} ->
                     {auto m : Ref MD Metadata} ->
                     {auto o : Ref ROpts REPLOpts} ->
                     List Name -> PiInfo PTerm -> Core (PiInfo RawImp)
  mapDesugarPiInfo ps = PiInfo.traverse (desugar AnyExpr ps)

  displayFixity : Maybe Visibility -> BindingModifier -> Fixity -> Nat -> OpStr -> String
  displayFixity Nothing NotBinding fix prec op = "\{show fix} \{show prec} \{show op}"
  displayFixity Nothing bind fix prec op = "\{show bind} \{show fix} \{show prec} \{show op}"
  displayFixity (Just vis) NotBinding fix prec op = "\{show vis} \{show fix} \{show prec} \{show op}"
  displayFixity (Just vis) bind fix prec op = "\{show vis} \{show bind} \{show fix} \{show prec} \{show op}"

  verifyTotalityModifiers : {auto c : Ref Ctxt Defs} ->
                            FC -> List FnOpt -> Core ()
  verifyTotalityModifiers fc opts =
    when (count isTotalityReq opts > 1) $ do
      let totalities = sort $ mapMaybe extractTotality opts
      let dedupTotalities = dedup totalities
      defaultTotality <- getDefaultTotalityOption
      throw $ GenericMsgSol fc "Multiple totality modifiers" "Possible solutions" $
        catMaybes $
          [ checkDuplicates totalities dedupTotalities
          , checkCompability dedupTotalities
          , checkDefault defaultTotality dedupTotalities
          ]
    where
      showModifiers : Show a => List a -> String
      showModifiers = concat . intersperse ", " . map (\s => "`\{show s}`")

      checkCompability : List TotalReq -> Maybe String
      checkCompability totalities =
        toMaybe (length totalities > 1) $
          "Leave only one modifier out of " ++ showModifiers totalities

      checkDuplicates : List TotalReq -> List TotalReq -> Maybe String
      checkDuplicates totalities dedupTotalities =
        toMaybe (totalities /= dedupTotalities) $ do
          let repeated = filter (\x => count (x ==) totalities > 1) dedupTotalities
          "Remove duplicates of " ++ showModifiers repeated

      checkDefault : TotalReq -> List TotalReq -> Maybe String
      checkDefault def totalities =
        toMaybe (def `elem` totalities) $
          "Remove modifiers " ++ showModifiers totalities ++
          ", resulting in the default totality of " ++ showModifiers [def]

  -- Given a high level declaration, return a list of TTImp declarations
  -- which process it, and update any necessary state on the way.
  export
  desugarDecl : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto m : Ref MD Metadata} ->
                {auto o : Ref ROpts REPLOpts} ->
                List Name -> PDecl -> Core (List ImpDecl)
  desugarDecl ps claim@(MkWithData _ (PClaim (MkPClaim rig vis fnopts ty)))
      = do opts <- traverse (desugarFnOpt ps) fnopts
           verifyTotalityModifiers claim.fc opts

           types <- desugarType ps ty
           pure $ flip (map {f = List, b = ImpDecl}) types $ \ty' =>
                      IClaim (MkFCVal claim.fc $ MkIClaimData rig vis opts ty')

  desugarDecl ps (MkWithData fc (PDef clauses))
  -- The clauses won't necessarily all be from the same function, so split
  -- after desugaring, by function name, using collectDefs from RawImp
      = do ncs <- traverse (desugarClause ps False) clauses
           defs <- traverse (uncurry $ toIDef . fromJust) ncs
           pure (collectDefs defs)
    where
      toIDef : Name -> ImpClause -> Core ImpDecl
      toIDef nm (PatClause fc lhs rhs)
          = pure $ IDef fc nm [PatClause fc lhs rhs]
      toIDef nm (WithClause fc lhs rig rhs prf flags cs)
          = pure $ IDef fc nm [WithClause fc lhs rig rhs prf flags cs]
      toIDef nm (ImpossibleClause fc lhs)
          = pure $ IDef fc nm [ImpossibleClause fc lhs]

  desugarDecl ps dat@(MkWithData _ $ PData doc vis mbtot ddecl)
      = pure [IData dat.fc vis mbtot !(desugarData ps doc ddecl)]

  desugarDecl ps pp@(MkWithData _ $ PParameters params pds)
      = do
           params' <- getArgs params
           let paramList = forget params'
           let paramNames = map (.name.val) paramList
           pds' <- traverse (desugarDecl (ps ++ paramNames)) pds
           -- Look for implicitly bindable names in the parameters
           pnames <- ifThenElse (not !isUnboundImplicits) (pure [])
             $ map concat
             $ for (map (boundType . val) paramList)
             $ findUniqueBindableNames pp.fc True (ps ++ paramNames) []

           let paramsb = map {f = List1} (map {f = WithData _} (mapType (doBind pnames))) params'
           pure [IParameters pp.fc paramsb (concat pds')]
      where
        getArgs : Either (List1 PlainBinder)
                         (List1 PBinder) ->
                         Core (List1 (ImpParameter' RawImp))
        getArgs (Left params)
          = traverseList1 (\ty => do
              ty' <- desugar AnyExpr ps ty.val
              pure (Mk [top, ty.name] (MkPiBindData Explicit ty'))) params
        getArgs (Right params)
          = join <$> traverseList1 (\(MkPBinder info (MkBasicMultiBinder rig n ntm)) => do
              tm' <- desugar AnyExpr ps ntm
              i' <- traverse (desugar AnyExpr ps) info
              let allbinders = map (\nn => Mk [rig, nn] (MkPiBindData i' tm')) n
              pure allbinders) params

  desugarDecl ps use@(MkWithData _ $ PUsing uimpls uds)
      = do syn <- get Syn
           let oldu = usingImpl syn
           uimpls' <- traverse (\ ntm => do tm' <- desugar AnyExpr ps (snd ntm)
                                            btm <- bindTypeNames use.fc oldu ps tm'
                                            pure (fst ntm, btm)) uimpls
           put Syn ({ usingImpl := uimpls' ++ oldu } syn)
           uds' <- traverse (desugarDecl ps) uds
           update Syn { usingImpl := oldu }
           pure (concat uds')
  desugarDecl ps int@(MkWithData _ $ PInterface vis cons_in tn doc params det conname body)
      = do addDocString tn doc
           let paramNames = concatMap (map val . forget . names) params

           let cons = concatMap expandConstraint cons_in
           cons' <- traverse (\ ntm => do tm' <- desugar AnyExpr (ps ++ paramNames)
                                                         (snd ntm)
                                          pure (fst ntm, tm')) cons
           params' <- concat <$> traverse (\ (MkBasicMultiBinder rig nm tm) =>
                         do tm' <- desugar AnyExpr ps tm
                            pure $ map (\n => (n, (rig, tm'))) (forget nm))
                      params
           let _ = the (List (WithFC Name, RigCount, RawImp)) params'
           -- Look for bindable names in all the constraints and parameters
           let mnames = map dropNS (definedIn (map val body))
           bnames <- ifThenElse (not !isUnboundImplicits) (pure [])
             $ map concat
             $ for (map Builtin.snd cons' ++ map (snd . snd) params')
             $ findUniqueBindableNames int.fc True (ps ++ mnames ++ paramNames) []

           let paramsb = map (\ (nm, (rig, tm)) =>
                                 let tm' = doBind bnames tm in
                                 (nm.val, (rig, tm')))
                         params'
           let consb = map (\ (nm, tm) => (nm, doBind bnames tm)) cons'

           body' <- traverse (desugarDecl (ps ++ mnames ++ paramNames)) body
           pure [IPragma int.fc (maybe [tn] (\n => [tn, n.val]) conname)
                            (\nest, env =>
                              elabInterface int.fc vis env nest consb
                                            tn paramsb det conname
                                            (concat body'))]
    where
      -- Turns pairs in the constraints to individual constraints. This
      -- is a bit of a hack, but it's necessary to build parent constraint
      -- chasing functions correctly
      pairToCons : PTerm -> List PTerm
      pairToCons (PPair _ l r) = pairToCons l ++ pairToCons r
      pairToCons t = [t]

      expandConstraint : (Maybe Name, PTerm) -> List (Maybe Name, PTerm)
      expandConstraint (Just n, t) = [(Just n, t)]
      expandConstraint (Nothing, p)
          = map (\x => (Nothing, x)) (pairToCons p)

  desugarDecl ps impl@(MkWithData _ $ PImplementation vis fnopts pass is cons tn params impln nusing body)
      = do opts <- traverse (desugarFnOpt ps) fnopts
           verifyTotalityModifiers impl.fc opts

           is' <- for is $ traverse (\ bind =>
                     do tm' <- desugar AnyExpr ps bind.boundType
                        pi' <- mapDesugarPiInfo ps bind.info
                        pure (MkPiBindData pi' tm'))
           cons' <- for cons $ \ (n, tm) =>
                     do tm' <- desugar AnyExpr ps tm
                        pure (n, tm')
           params' <- traverse (desugar AnyExpr ps) params
           let _ = the (List RawImp) params'
           -- Look for bindable names in all the constraints and parameters
           bnames <- ifThenElse (not !isUnboundImplicits) (pure [])
             $ map concat
             $ for (map snd cons' ++ params')
             $ findUniqueBindableNames impl.fc True ps []

           let paramsb = map (doBind bnames) params'
           let isb = map (map (mapType (doBind bnames))) is'
           let consb = map (map (doBind bnames)) cons'

           body' <- maybe (pure Nothing)
                          (\b => do b' <- traverse (desugarDecl ps) b
                                    pure (Just (concat b'))) body
           -- calculate the name of the implementation, if it's not explicitly
           -- given.
           let impname = maybe (mkImplName impl.fc tn paramsb) id impln

           pure [IPragma impl.fc [impname]
                            (\nest, env =>
                               elabImplementation impl.fc vis opts pass env nest isb consb
                                                  tn paramsb (isNamed impln)
                                                  impname nusing
                                                  body')]
    where
      isNamed : Maybe a -> Bool
      isNamed Nothing = False
      isNamed (Just _) = True

  desugarDecl ps rec@(MkWithData fc $ PRecord doc vis mbtot (MkPRecordLater tn params))
      = desugarDecl ps (MkWithData fc $ PData doc vis mbtot (MkPLater rec.fc tn (mkRecType params)))
    where
      mkRecType : List PBinder -> PTerm
      mkRecType [] = PType rec.fc
      mkRecType (MkPBinder p (MkBasicMultiBinder c (n ::: []) t) :: ts)
        = PPi rec.fc c p (Just n.val) t (mkRecType ts)
      mkRecType (MkPBinder p (MkBasicMultiBinder c (n ::: x :: xs) t) :: ts)
        = PPi rec.fc c p (Just n.val) t (mkRecType (MkPBinder p (MkBasicMultiBinder c (x ::: xs) t) :: ts))
  desugarDecl ps rec@(MkWithData _ $ PRecord doc vis mbtot (MkPRecord tn params opts conname_in fields))
      = do addDocString tn doc
           params' <- concat <$> traverse (\ (MkPBinder info (MkBasicMultiBinder rig names tm)) =>
                          do tm' <- desugar AnyExpr ps tm
                             p'  <- mapDesugarPiInfo ps info
                             let allBinders = map (\nm => Mk [rig, nm] (MkPiBindData p' tm')) (forget names)
                             pure allBinders)
                        params
           let _ = the (List ImpParameter) params'
           let fnames = concat $ map getfname fields
           let paramNames = concatMap (map val . forget . names . bind) params
           let _ = the (List Name) fnames
           -- Look for bindable names in the parameters

           let bnames = if !isUnboundImplicits
                        then concatMap (findBindableNames True
                                         (ps ++ fnames ++ paramNames) [])
                                       (map (boundType . val) params')
                        else []
           let _ = the (List (Name, Name)) bnames

           let paramsb = map (map (mapType (doBind bnames))) params'
           let _ = the (List ImpParameter) paramsb
           let recName = nameRoot tn
           fields' <- traverse (desugarField (ps ++ fnames ++ paramNames)
                                             (mkNamespace recName))
                               fields
           let _ = the (List $ List IField) fields'
           let conname = maybe (mkConName tn) val conname_in
           whenJust (get "doc" <$> conname_in) (addDocString conname)
           let _ = the Name conname
           pure [IRecord rec.fc (Just recName)
                         vis mbtot (Mk [rec.fc] $ MkImpRecord (Mk [NoFC tn] paramsb) (Mk [NoFC conname, opts] (concat fields')))]
    where
      getfname : PField -> List Name
      getfname x = map val x.names

      mkConName : Name -> Name
      mkConName (NS ns (UN n))
        = let str = displayUserName n in
          NS ns (DN str (MN ("__mk" ++ str) 0))
      mkConName n = DN (show n) (MN ("__mk" ++ show n) 0)

  desugarDecl ps fx@(MkWithData _ $ PFixity (MkPFixityData vis binding fix prec opNames))
      = flip (Core.traverseList1_ {b = Unit}) opNames (\opName : OpStr => do
           unless (checkValidFixity binding fix prec)
             (throw $ GenericMsgSol fx.fc
                 "Invalid fixity, \{binding} operator must be infixr 0." "Possible solutions"
                 [ "Make it `infixr 0`: `\{binding} infixr 0 \{show opName}`"
                 , "Remove the binding keyword: `\{fix} \{show prec} \{show opName}`"
                 ])
           when (isDefaulted vis) $
             let adjustedExport = displayFixity (Just Export) binding fix prec opName
                 adjustedPrivate = displayFixity (Just Private) binding fix prec opName
                 originalFixity = displayFixity Nothing binding fix prec opName
             in recordWarning $ GenericWarn fx.fc """
               Fixity declaration '\{originalFixity}' does not have an export modifier, and
               will become private by default in a future version.
               To expose it outside of its module, write '\{adjustedExport}'. If you
               intend to keep it private, write '\{adjustedPrivate}'.
               """
           ctx <- get Ctxt
           -- We update the context of fixities by adding a namespaced fixity
           -- given by the current namespace and its fixity name.
           -- This allows fixities to be stored along with the namespace at their
           -- declaration site and detect and handle ambiguous fixities
           let updatedNS = NS (mkNestedNamespace (Just ctx.currentNS) (show fix))
                              (UN $ Basic $ nameRoot opName.toName)

           update Syn
             { fixities $=
               addName updatedNS
                 (MkFixityInfo fx.fc (collapseDefault vis) binding fix prec) })
        >> pure []
  desugarDecl ps d@(MkWithData _ $ PFail mmsg ds)
      = do -- save the state: the content of a failing block should be discarded
           ust <- get UST
           md <- get MD
           opts <- get ROpts
           syn <- get Syn
           defs <- branch
           log "desugar.failing" 20 $ "Desugaring the block:\n" ++ show d.val
           -- See whether the desugaring phase fails and return
           -- * Right ds                            if the desugaring succeeded
           --                                       the error will have to come later in the pipeline
           -- * Left Nothing                        if the block correctly failed
           -- * Left (Just (FailingWrongError err)) if the block failed with the wrong error
           result <- catch
             (do -- run the desugarer
                 ds <- traverse (desugarDecl ps) ds
                 pure (Right (concat ds)))
             (\err => do -- no message: any error will do
                         let Just msg = mmsg
                             | _ => pure (Left Nothing)
                         -- otherwise have a look at the displayed message
                         log "desugar.failing" 10 $ "Failing block based on \{show msg} failed with \{show err}"
                         test <- checkError msg err
                         pure $ Left $ do
                              -- Unless the error is the expected one
                              guard (not test)
                              -- We should complain we had the wrong one
                              pure (FailingWrongError d.fc msg (err ::: [])))
           -- Reset the state
           put UST ust
           md' <- get MD
           put MD ({ semanticHighlighting := semanticHighlighting md'
                   , semanticAliases := semanticAliases md'
                   , semanticDefaults := semanticDefaults md'
                   } md)
           put Syn syn
           put Ctxt defs
           -- either fail or return the block that should fail during the elab phase
           case the (Either (Maybe Error) (List ImpDecl)) result of
             Right ds => [IFail d.fc mmsg ds] <$ log "desugar.failing" 20 "Success"
             Left Nothing => [] <$ log "desugar.failing" 20 "Correctly failed"
             Left (Just err) => throw err
  desugarDecl ps (MkWithData _ $ PMutual ds)
      = do let (tys, defs) = splitMutual ds
           mds' <- traverse (desugarDecl ps) (tys ++ defs)
           pure (concat mds')
  desugarDecl ps n@(MkWithData _ $ PNamespace ns decls)
      = withExtendedNS ns $ do
           ds <- traverse (desugarDecl ps) decls
           pure [INamespace n.fc ns (concat ds)]
  desugarDecl ps ts@(MkWithData _ $ PTransform n lhs rhs)
      = do (bound, blhs) <- bindNames False !(desugar LHS ps lhs)
           rhs' <- desugar AnyExpr (bound ++ ps) rhs
           pure [ITransform ts.fc (UN $ Basic n) blhs rhs']
  desugarDecl ps el@(MkWithData _ $ PRunElabDecl tm)
      = do tm' <- desugar AnyExpr ps tm
           pure [IRunElabDecl el.fc tm']
  desugarDecl ps dir@(MkWithData _ $ PDirective d)
      = let fc = dir.fc in case d of
             Hide (HideName n) => pure [IPragma fc [] (\nest, env => hide fc n)]
             Hide (HideFixity fx n) => pure [IPragma fc [] (\_, _ => removeFixity fc fx n)]
             Unhide n => pure [IPragma fc [] (\nest, env => unhide fc n)]
             Logging i => pure [ILog ((\ i => (topics i, verbosity i)) <$> i)]
             LazyOn a => pure [IPragma fc [] (\nest, env => lazyActive a)]
             UnboundImplicits a => do
               setUnboundImplicits a
               pure [IPragma fc [] (\nest, env => setUnboundImplicits a)]
             PrefixRecordProjections b => do
               pure [IPragma fc [] (\nest, env => setPrefixRecordProjections b)]
             AmbigDepth n => pure [IPragma fc [] (\nest, env => setAmbigLimit n)]
             TotalityDepth n => pure [IPragma fc [] (\next, env => setTotalLimit n)]
             AutoImplicitDepth n => pure [IPragma fc [] (\nest, env => setAutoImplicitLimit n)]
             NFMetavarThreshold n => pure [IPragma fc [] (\nest, env => setNFThreshold n)]
             SearchTimeout n => pure [IPragma fc [] (\nest, env => setSearchTimeout n)]
             PairNames ty f s => pure [IPragma fc [] (\nest, env => setPair fc ty f s)]
             RewriteName eq rw => pure [IPragma fc [] (\nest, env => setRewrite fc eq rw)]
             PrimInteger n => pure [IPragma fc [] (\nest, env => setFromInteger n)]
             PrimString n => pure [IPragma fc [] (\nest, env => setFromString n)]
             PrimChar n => pure [IPragma fc [] (\nest, env => setFromChar n)]
             PrimDouble n => pure [IPragma fc [] (\nest, env => setFromDouble n)]
             PrimTTImp n => pure [IPragma fc [] (\nest, env => setFromTTImp n)]
             PrimName n => pure [IPragma fc [] (\nest, env => setFromName n)]
             PrimDecls n => pure [IPragma fc [] (\nest, env => setFromDecls n)]
             CGAction cg dir => pure [IPragma fc [] (\nest, env => addDirective cg dir)]
             Names n ns => pure [IPragma fc [] (\nest, env => addNameDirective fc n ns)]
             StartExpr tm => pure [IPragma fc [] (\nest, env => throw (InternalError "%start not implemented"))] -- TODO!
             Overloadable n => pure [IPragma fc [] (\nest, env => setNameFlag fc n Overloadable)]
             Extension e => pure [IPragma fc [] (\nest, env => setExtension e)]
             DefaultTotality tot => pure [IPragma fc [] (\_, _ => setDefaultTotalityOption tot)]
             ForeignImpl n cs => do
               cs' <- traverse (desugar AnyExpr ps) cs
               pure [IPragma fc [] (\nest, env => do
                      defs <- get Ctxt
                      calls <- traverse getFnString cs'
                      [(n',_,gdef)] <- lookupCtxtName n (gamma defs)
                        | [] => throw (UndefinedName fc n)
                        | xs => throw (AmbiguousName fc (map fst xs))
                      let ForeignDef arity xs = gdef.definition
                        | _ => throw (GenericMsg fc "\{show n} is not a foreign definition")

                      update Ctxt { options->foreignImpl $= (map (n',) calls ++) }
                    )]
  desugarDecl ps bt@(MkWithData _ $ PBuiltin type name) = pure [IBuiltin bt.fc type name]

  export
  desugarDo : {auto s : Ref Syn SyntaxInfo} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto o : Ref ROpts REPLOpts} ->
              Side -> List Name -> Maybe Namespace -> PTerm -> Core RawImp
  desugarDo s ps doNamespace tm
      = do b <- newRef Bang (initBangs doNamespace)
           tm' <- desugarB s ps tm
           bd <- get Bang
           pure $ bindBangs (bangNames bd) doNamespace tm'

  export
  desugar : {auto s : Ref Syn SyntaxInfo} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto o : Ref ROpts REPLOpts} ->
            Side -> List Name -> PTerm -> Core RawImp

  desugar s ps tm = desugarDo s ps Nothing tm
