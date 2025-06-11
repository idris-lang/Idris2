module TTImp.Elab.BindingApp

import Core.Core
import Core.Context
import Core.Env
import Core.FC
import Core.Unify
import Core.Metadata
import Core.Name
import Core.Normalise
import Core.WithName

import TTImp.Elab.Check
import TTImp.TTImp

import Idris.REPL.Opts
import Idris.Syntax


keepBinding : List GlobalDef -> List GlobalDef
keepBinding = filter (\x => x.bindingMode /= NotBinding)

parameters (originalName : WithFC Name)
  checkUnique : List GlobalDef -> Core GlobalDef
  checkUnique [ def ] = pure def
  checkUnique [] = throw $ UndefinedName originalName.fc originalName.val
  checkUnique defs = throw $ AmbiguousName originalName.fc (map fullname defs)

  typecheckCandidates : List GlobalDef -> Core (List GlobalDef)
  typecheckCandidates xs = pure xs -- todo

  checkBinding : (candidates : List GlobalDef) -> Core GlobalDef
  checkBinding candidates = do
    let bindingCandidates = keepBinding candidates
    coreLift $ putStrLn "potential candidates for identifer : \{show bindingCandidates}"
    wellTypedCandidates <- typecheckCandidates bindingCandidates
    checkUnique bindingCandidates


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
  WithFC Name -> WithFC (WithName RawImp) -> WithFC RawImp ->
  Core (Term vars, Glued vars)
checkBindingApplication rig info nest env nm bind scope = do
  ctx <- get Ctxt
  coreLift $ putStrLn "checking if \{show nm.val} is binding"
  defs <- lookupCtxtName nm.val (gamma ctx)
  firstArg <- checkBinding nm (map (snd . snd) defs)
  -- check if the name in context is marked as binding
  -- - if it's typebind, check the bound variable is a Type
  -- - if it's autobind, infer the type from the scope
  --   - If the type is given explicitly, use that
  -- - if it's neither, report the error
  ?TODONext

