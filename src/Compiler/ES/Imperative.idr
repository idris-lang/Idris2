module Compiler.ES.Imperative

import public Compiler.ES.ImperativeAst

import Data.List

import Compiler.Common
import Compiler.CompileExpr

import public Core.Context

import Compiler.ES.RemoveUnused
import Compiler.ES.TailRec


mutual
  isNameUsed : Name -> NamedCExp -> Bool
  isNameUsed name (NmLocal fc n) = n == name
  isNameUsed name (NmRef fc n) = n == name
  isNameUsed name (NmLam fc n e) = isNameUsed name e
  isNameUsed name (NmApp fc x args) = isNameUsed name x || any (isNameUsed name) args
  isNameUsed name (NmPrimVal fc c) = False
  isNameUsed name (NmOp fc op args) = any (isNameUsed name) args
  isNameUsed name (NmConCase fc sc alts def) = isNameUsed name sc || any (isNameUsedConAlt name) alts  || maybe False (isNameUsed name) def
  isNameUsed name (NmConstCase fc sc alts def) = isNameUsed name sc || any (isNameUsedConstAlt name) alts  || maybe False (isNameUsed name) def
  isNameUsed name (NmExtPrim fc p args) = any (isNameUsed name) args
  isNameUsed name (NmCon fc x t args) = any (isNameUsed name) args
  isNameUsed name (NmDelay fc t) = isNameUsed name t
  isNameUsed name (NmForce fc t) = isNameUsed name t
  isNameUsed name (NmLet fc x val sc) =
    if x == name then isNameUsed name val
      else isNameUsed name val || isNameUsed name sc
  isNameUsed name (NmErased fc) = False
  isNameUsed name (NmCrash fc msg) = False

  isNameUsedConAlt : Name -> NamedConAlt -> Bool
  isNameUsedConAlt name (MkNConAlt n t args exp) = isNameUsed name exp

  isNameUsedConstAlt : Name -> NamedConstAlt -> Bool
  isNameUsedConstAlt name (MkNConstAlt c exp) = isNameUsed name exp

data Imps : Type where

record ImpSt where
  constructor MkImpSt
  nextName : Int

genName : {auto c : Ref Imps ImpSt} -> Core Name
genName =
  do
    s <- get Imps
    let i = nextName s
    put Imps (record { nextName = i + 1 } s)
    pure $ MN "imp_gen" i

mutual

  pairToReturn : (toReturn : Bool) -> (ImperativeStatement, ImperativeExp) ->
                     Core (ifThenElse toReturn ImperativeStatement  (ImperativeStatement, ImperativeExp))
  pairToReturn False (s, e) = pure (s, e)
  pairToReturn True (s, e) = pure $ s <+> ReturnStatement e

  expToReturn : (toReturn : Bool) -> ImperativeExp ->
                     Core (ifThenElse toReturn ImperativeStatement  (ImperativeStatement, ImperativeExp))
  expToReturn False e = pure $ (DoNothing, e)
  expToReturn True e = pure $ ReturnStatement e

  impVectExp : {auto c : Ref Imps ImpSt} -> Vect n NamedCExp -> Core (ImperativeStatement, Vect n ImperativeExp)
  impVectExp args =
    do
      a <- traverseVect (impExp False) args
      pure (concat (map fst a), map snd a)

  impListExp : {auto c : Ref Imps ImpSt} -> List NamedCExp -> Core (ImperativeStatement, List ImperativeExp)
  impListExp args =
    do
      a <- traverse (impExp False) args
      pure (concat (map fst a), map snd a)

  impExp : {auto c : Ref Imps ImpSt} -> (toReturn : Bool) -> NamedCExp ->
                     Core (ifThenElse toReturn ImperativeStatement  (ImperativeStatement, ImperativeExp))
  impExp toReturn (NmLocal fc n) = expToReturn toReturn $ IEVar n
  impExp toReturn (NmRef fc n) = expToReturn toReturn $ IEVar n
  impExp toReturn (NmLam fc n e) = expToReturn toReturn $ IELambda [n] !(impExp True e)
  impExp toReturn (NmApp fc x args) =
    do
      (s1, f) <- impExp False x
      (s2, a) <- impListExp args
      pairToReturn toReturn (s1 <+> s2, IEApp f a)
  impExp toReturn (NmPrimVal fc c) = expToReturn toReturn $ IEConstant c
  impExp toReturn (NmOp fc op args) =
    do
      (s, a) <- impVectExp args
      pairToReturn toReturn (s, IEPrimFn op a)
  impExp False (NmConCase fc sc alts def) =
    do
      (s1, exp) <- impExp False sc
      res <- genName
      swalts <- traverse (impConAlt (Just res) exp) alts
      swdef <- case def of
                Nothing => pure $ ErrorStatement $ "unhandled con case on " ++ show fc
                Just x =>
                  do
                    (sd, r) <- impExp False x
                    pure $ sd <+> MutateStatement res r
      let switch = SwitchStatement (IEConstructorHead exp) swalts (Just swdef)
      pure (s1 <+> LetDecl res Nothing <+> switch, IEVar res)
  impExp True (NmConCase fc sc alts def) =
    do
      (s1, exp) <- impExp False sc
      swalts <- traverse (impConAlt Nothing exp) alts
      swdef <- case def of
                Nothing => pure $ ErrorStatement $ "unhandled con case on " ++ show fc
                Just x => impExp True x
      let switch = SwitchStatement (IEConstructorHead exp) swalts (Just swdef)
      pure (s1 <+> switch)
  impExp False (NmConstCase fc sc alts def) =
    do
      (s1, exp) <- impExp False sc
      res <- genName
      swalts <- traverse (impConstAlt $ Just res) alts
      swdef <- case def of
                Nothing => pure $ ErrorStatement $ "unhandled const case on " ++ show fc
                Just x =>
                  do
                    (sd, r) <- impExp False x
                    pure $ sd <+> MutateStatement res r
      let switch = SwitchStatement exp swalts (Just swdef)
      pure (s1 <+> LetDecl res Nothing <+> switch, IEVar res)
  impExp True (NmConstCase fc sc alts def) =
    do
      (s1, exp) <- impExp False sc
      swalts <- traverse (impConstAlt Nothing) alts
      swdef <- case def of
                Nothing => pure $ ErrorStatement $ "unhandled const case on " ++ show fc
                Just x => impExp True x
      let switch = SwitchStatement exp swalts (Just swdef)
      pure $ s1 <+> switch
  impExp toReturn (NmExtPrim fc p args) =
    do
      (s, a) <- impListExp args
      pairToReturn toReturn (s, IEPrimFnExt p a)
  impExp toReturn (NmCon fc x tag args) =
    do
      (s, a) <- impListExp args
      pairToReturn toReturn (s, IEConstructor (impTag x tag) a)
  impExp toReturn (NmDelay fc t) =
    do
      (s, x) <- impExp False t
      pairToReturn toReturn (s, IEDelay x)
  impExp toReturn (NmForce fc t) =
    do
      (s, x) <- impExp False t
      pairToReturn toReturn (s, IEForce x)
  impExp toReturn (NmLet fc x val sc) =
    do
      (s1, v) <- impExp False val
      (s2, sc_) <- impExp False sc
      if isNameUsed x sc
        then do
          x_ <- genName
          let reps = [(x, IEVar x_)]
          let s2_ = replaceNamesExpS reps s2
          let sc__ = replaceNamesExp reps sc_
          let decl = ConstDecl x_ v
          pairToReturn toReturn (s1 <+> decl <+> s2_, sc__)
        else do
          let decl = EvalExpStatement v
          pairToReturn toReturn (s1 <+> decl <+> s2, sc_)
  impExp toReturn (NmErased fc) =
    expToReturn toReturn $ IENull
  impExp toReturn (NmCrash fc msg) =
    pairToReturn toReturn (ErrorStatement msg, IENull)

  impTag : Name -> Maybe Int -> Either Int String
  impTag n Nothing = Right $ show n
  impTag n (Just i) = Left i

  impConAlt : {auto c : Ref Imps ImpSt} -> Maybe Name -> ImperativeExp -> NamedConAlt -> Core (ImperativeExp, ImperativeStatement)
  impConAlt (Just res) target (MkNConAlt n tag args exp) =
    do
      (s, r) <- impExp False exp
      let nargs = length args
      let reps = zipWith (\i, n => (n, IEConstructorArg (cast i) target)) [1..nargs] args
      pure (IEConstructorTag (impTag n tag), replaceNamesExpS reps $ s <+> MutateStatement res r)
  impConAlt Nothing target (MkNConAlt n tag args exp) =
    do
      (s, r) <- impExp False exp
      let nargs = length args
      let reps = zipWith (\i, n => (n, IEConstructorArg (cast i) target)) [1..nargs] args
      pure (IEConstructorTag (impTag n tag), replaceNamesExpS reps $ s <+> ReturnStatement r)

  impConstAlt : {auto c : Ref Imps ImpSt} -> Maybe Name -> NamedConstAlt -> Core (ImperativeExp, ImperativeStatement)
  impConstAlt (Just res) (MkNConstAlt c exp) =
    do
      (s, r) <- impExp False exp
      pure (IEConstant c, s <+> MutateStatement res r)
  impConstAlt Nothing (MkNConstAlt c exp) =
    do
      (s, r) <- impExp False exp
      pure (IEConstant c, s <+> ReturnStatement r)

getImp : {auto c : Ref Imps ImpSt} -> (Name, FC, NamedDef) -> Core ImperativeStatement
getImp (n, fc, MkNmFun args exp) =
  pure $ FunDecl fc n args !(impExp True exp)
getImp (n, fc, MkNmError exp) =
  throw $ (InternalError $ show exp)
getImp (n, fc, MkNmForeign cs args ret) =
  pure $ ForeignDecl fc n cs args ret
getImp (n, fc, MkNmCon _ _ _) =
  pure DoNothing

export
compileToImperative : Ref Ctxt Defs -> ClosedTerm -> Core (ImperativeStatement, ImperativeStatement)
compileToImperative c tm =
  do
    cdata <- getCompileData Cases tm
    let ndefs = namedDefs cdata
    let ctm = forget (mainExpr cdata)
    s <- newRef Imps (MkImpSt 0)
    lst_defs <- traverse getImp (defsUsedByNamedCExp ctm ndefs)
    let defs = concat lst_defs
    let defs_optim = tailRecOptim defs
    (s, main) <- impExp False ctm
    pure $ (defs_optim, s <+> EvalExpStatement main)
