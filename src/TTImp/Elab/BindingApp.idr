module TTImp.Elab.BindingApp

import Core.Core
import Core.Context
import Core.Env
import Core.FC
import Core.Unify
import Core.Metadata
import Core.Name
import Core.Normalise

import TTImp.Elab.Check
import TTImp.Elab.App
import TTImp.TTImp

import Idris.REPL.Opts
import Idris.Syntax


keepBinding : BindingModifier -> List GlobalDef -> List GlobalDef
keepBinding mode = filter (\x => x.bindingMode == mode)

parameters (originalName : WithFC Name) {auto c : Ref Ctxt Defs}
  checkUnique : List GlobalDef -> Core GlobalDef
  checkUnique [ def ] = pure def
  checkUnique [] = throw $ UndefinedName originalName.fc originalName.val
  checkUnique defs = throw $ AmbiguousName originalName.fc (map fullname defs)

  typecheckCandidates : List GlobalDef -> Core (List GlobalDef)
  typecheckCandidates xs = pure xs -- todo

  checkBinding : (mode : BindingModifier) -> (candidates : List GlobalDef) -> Core GlobalDef
  checkBinding mode candidates = do
    let bindingCandidates = keepBinding mode candidates
    log "elab.bindApp"  10 $ "Potential candidates for binding identifer : \{show (map fullname bindingCandidates)}"
    wellTypedCandidates <- typecheckCandidates bindingCandidates
    checkUnique bindingCandidates

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

