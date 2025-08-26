module TTImp.Elab.BindingApp

import Core.Core
import Core.Context
import Core.Env
import Core.FC
import Core.Unify
import Core.Metadata
import Core.Name
import Core.Normalise

import Data.List

import TTImp.Elab.Check
import TTImp.Elab.App
import TTImp.TTImp

import Idris.REPL.Opts
import Idris.Syntax



record BindingModes (a : Type) where
  constructor MkBindingModes
  everythingMatches : List a
  bindingDoesNotMatch : List a
  notBinding : List a

keepBinding : BindingModifier -> List GlobalDef -> BindingModes GlobalDef
keepBinding mode = foldl sortBinding (MkBindingModes [] [] [])
  where
    sortBinding : BindingModes GlobalDef -> GlobalDef -> BindingModes GlobalDef
    sortBinding modes def = if def.bindingMode == mode
                               then {everythingMatches $= (def ::)} modes
                               else if def.bindingMode == NotBinding
                               then {notBinding $= (def ::)} modes
                               else {bindingDoesNotMatch $= (def ::)} modes


parameters (originalName : WithFC Name) (mode : BindingModifier) {auto c : Ref Ctxt Defs}
  checkUnique : BindingModes GlobalDef -> Core GlobalDef
  checkUnique (MkBindingModes [ def ] _ _ ) = pure def
  checkUnique (MkBindingModes [] may others) = do
      coreLift $ putStrLn (show $ map fullname others)
      throw $ BindingApplicationMismatch originalName.fc mode (map fullname may) (map fullname others)
  checkUnique (MkBindingModes defs _ _) = throw $ AmbiguousName originalName.fc (map fullname defs)

  typecheckCandidates : List GlobalDef -> Core (List GlobalDef)
  typecheckCandidates xs = pure xs -- todo: emit errors when the type doesn't match

  checkBinding : (candidates : List GlobalDef) -> Core GlobalDef
  checkBinding candidates = do
    log "elab.bindApp"  10 $ "Potential candidates for binding identifer : \{show (map fullname candidates)}"
    log "elab.bindApp"  10 $ "Checking if candidates have binding \{show mode}"
    let candidates = keepBinding mode candidates
    log "elab.bindApp"  10 $ "Final list of binding identifers : \{show (map fullname candidates.everythingMatches)}"
    -- wellTypedCandidates <- typecheckCandidates bindingCandidates
    checkUnique candidates

typeForBinder : BindingInfo RawImp -> FC -> RawImp
typeForBinder (BindType name type) = const type
typeForBinder (BindExpr name expr) = flip Implicit False
typeForBinder (BindExplicitType name type expr) = const type


buildLam : BindingInfo RawImp -> Maybe Name
buildLam (BindType (IVar _ name) type) = Just name
buildLam (BindExpr (IVar _ name) expr) =  Just name
buildLam (BindExplicitType (IVar _ name) type expr) =  Just name
buildLam _ = Nothing

export
checkBindingApplication : {vars : _} ->
  {auto c : Ref Ctxt Defs} ->
  {auto m : Ref MD Metadata} ->
  {auto u : Ref UST UState} ->
  {auto e : Ref EST (EState vars)} ->
  {auto s : Ref Syn SyntaxInfo} ->
  {auto o : Ref ROpts REPLOpts} ->
  RigCount -> ElabInfo ->
  NestedNames vars -> Env Term vars ->
  WithFC Name -> WithFC (BindingInfo RawImp) -> WithFC RawImp ->
  Maybe (Glued vars) ->
  Core (Term vars, Glued vars)
checkBindingApplication rig info nest env nm bind scope exp = do
  ctx <- get Ctxt
  log "elab.bindApp" 10 $ "checking if \{show nm.val} is binding"
  defs <- lookupCtxtName nm.val (gamma ctx)
  firstArg <- checkBinding nm bind.val.getBindingMode (map (snd . snd) defs)
  let lam = ILam scope.fc top Explicit (buildLam bind.val) (typeForBinder bind.val bind.fc) scope.val
  let fc = fromMaybe EmptyFC (mergeFC nm.fc scope.fc)
  log "elab.bindApp" 10 $ "generating function \{show lam}"
  checkApp rig info nest env fc (IVar nm.fc nm.val) [ bind.val.getBoundExpr,  lam ] [] [] exp

