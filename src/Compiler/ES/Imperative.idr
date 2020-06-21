module Compiler.ES.Imperative

import public Data.Vect
import public Data.List

import Compiler.Common
import Compiler.CompileExpr

import public Core.Context
import public Core.TT

import Compiler.ES.RemoveUnused

import Debug.Trace

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

mutual
  public export
  data ImperativeExp = IEVar Name
                     | IELambda (List Name) ImperativeStatement
                     | IEApp ImperativeExp (List ImperativeExp)
                     | IEConstant Constant
                     | IEPrimFn (PrimFn arity) (Vect arity ImperativeExp)
                     | IEPrimFnExt Name (List ImperativeExp)
                     | IEConstructorHead ImperativeExp
                     | IEConstructorTag (Either Int String)
                     | IEConstructorArg Int ImperativeExp
                     | IEConstructor (Either Int String) (List ImperativeExp)
                     | IEDelay ImperativeExp
                     | IEForce ImperativeExp
                     | IENull

  public export
  data ImperativeStatement = DoNothing
                           | SeqStatement ImperativeStatement ImperativeStatement
                           | FunDecl FC Name (List Name) ImperativeStatement
                           | ForeignDecl Name (List String)
                           | ReturnStatement ImperativeExp
                           | SwitchStatement ImperativeExp (List (ImperativeExp, ImperativeStatement)) (Maybe ImperativeStatement)
                           | LetDecl Name (Maybe ImperativeExp)
                           | ConstDecl Name ImperativeExp
                           | MutateStatement Name ImperativeExp
                           | ErrorStatement String
                           | EvalExpStatement ImperativeExp
                           | CommentStatement String

Semigroup ImperativeStatement where
  DoNothing <+> y = y
  x <+> DoNothing = x
  x <+> y = SeqStatement x y

Monoid ImperativeStatement where
  neutral = DoNothing

mutual
  export
  Show ImperativeExp where
    show (IEVar n) =  "(IEVar " ++ show n ++ ")"
    show (IELambda args b) = "(IELambda " ++ show args ++ " " ++ show b ++ ")"
    show (IEApp f args) = "(IEApp " ++ show f ++ " " ++ show args ++ ")"
    show (IEConstant c) =  "(IEConstant " ++ show c ++ ")"
    show (IEPrimFn f args) = "(IEPrimFn " ++ show f ++ " " ++ show args ++ ")"
    show (IEPrimFnExt f args) = "(IEPrimFnExt " ++ show f ++ " " ++ show args ++ ")"
    show (IEConstructorHead c) =  "(IEConstructorHead " ++ show c ++ ")"
    show (IEConstructorTag t) =  "(IEConstructorTag " ++ show t ++ ")"
    show (IEConstructorArg i c) = "(IEConstructorArg " ++ show i ++ " " ++ show c ++ ")"
    show (IEConstructor i args) = "(IEConstructor " ++ show i ++ " " ++ show args ++ ")"
    show (IEDelay x) =  "(IEDelay " ++ show x ++ ")"
    show (IEForce x) =  "(IEForce " ++ show x ++ ")"
    show IENull = "IENull"

  export
  Show ImperativeStatement where
    show DoNothing = "DoNothing"
    show (SeqStatement x y) = show x ++ ";" ++ show y
    show (FunDecl fc n args b) = "\n\n" ++ "(FunDecl (" ++ show fc ++ ") " ++ show n ++ " " ++ show args ++ " " ++ show b ++ ")"
    show (ForeignDecl n path) = "(ForeignDecl " ++ show n ++ " " ++ show path ++")"
    show (ReturnStatement x) = "(ReturnStatement " ++ show x ++ ")"
    show (SwitchStatement e alts d) = "(SwitchStatement " ++ show e ++ " " ++ show alts ++ " " ++ show d ++ ")"
    show (LetDecl n v) = "(LetDecl " ++ show n ++ " " ++ show v ++ ")"
    show (ConstDecl n v) = "(ConstDecl " ++ show n ++ " " ++ show v ++ ")"
    show (MutateStatement n v) = "(MutateStatement " ++ show n ++ " " ++ show v ++ ")"
    show (ErrorStatement s) = "(ErrorStatement " ++ s ++ ")"
    show (EvalExpStatement x) =  "(EvalExpStatement " ++ show x ++ ")"
    show (CommentStatement x) = "(CommentStatement " ++ show x ++ ")"

mutual
  replaceNamesExp : List (Name, ImperativeExp) -> ImperativeExp -> ImperativeExp
  replaceNamesExp reps (IEVar n) =
    case lookup n reps of
      Nothing => IEVar n
      Just e => e
  replaceNamesExp reps (IELambda args body) =
    IELambda args $ replaceNamesExpS reps body
  replaceNamesExp reps (IEApp f args) =
    IEApp (replaceNamesExp reps f) (replaceNamesExp reps <$> args)
  replaceNamesExp reps (IEConstant c) =
    IEConstant c
  replaceNamesExp reps (IEPrimFn f args) =
    IEPrimFn f (replaceNamesExp reps <$> args)
  replaceNamesExp reps (IEPrimFnExt f args) =
    IEPrimFnExt f (replaceNamesExp reps <$> args)
  replaceNamesExp reps (IEConstructorHead e) =
    IEConstructorHead $ replaceNamesExp reps e
  replaceNamesExp reps (IEConstructorTag i) =
    IEConstructorTag i
  replaceNamesExp reps (IEConstructorArg i e) =
    IEConstructorArg i (replaceNamesExp reps e)
  replaceNamesExp reps (IEConstructor t args) =
    IEConstructor t (replaceNamesExp reps <$> args)
  replaceNamesExp reps (IEDelay e) =
    IEDelay $ replaceNamesExp reps e
  replaceNamesExp reps (IEForce e) =
    IEForce $ replaceNamesExp reps e
  replaceNamesExp reps IENull =
    IENull


  replaceNamesExpS : List (Name, ImperativeExp) -> ImperativeStatement -> ImperativeStatement
  replaceNamesExpS reps DoNothing =
    DoNothing
  replaceNamesExpS reps (SeqStatement x y) =
    SeqStatement (replaceNamesExpS reps x) (replaceNamesExpS reps y)
  replaceNamesExpS reps (FunDecl fc n args body) =
    FunDecl fc n args $ replaceNamesExpS reps body
  replaceNamesExpS reps (ForeignDecl n path) =
    ForeignDecl n path
  replaceNamesExpS reps (ReturnStatement e) =
    ReturnStatement $ replaceNamesExp reps e
  replaceNamesExpS reps (SwitchStatement s alts def) =
    let s_    = replaceNamesExp reps s
        alts_ = (\(e,b) => (replaceNamesExp reps e, replaceNamesExpS reps b)) <$> alts
        def_  = replaceNamesExpS reps <$> def
    in SwitchStatement s_ alts_ def_
  replaceNamesExpS reps (LetDecl n v) =
    LetDecl n $ replaceNamesExp reps <$> v
  replaceNamesExpS reps (ConstDecl n v) =
    ConstDecl n $ replaceNamesExp reps v
  replaceNamesExpS reps (MutateStatement n v) =
    MutateStatement n $ replaceNamesExp reps v
  replaceNamesExpS reps (ErrorStatement s) =
    ErrorStatement s
  replaceNamesExpS reps (EvalExpStatement x) =
    EvalExpStatement $ replaceNamesExp reps x
  replaceNamesExpS reps (CommentStatement x) =
    CommentStatement x

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

  expToFnBody : {auto c : Ref Imps ImpSt} -> NamedCExp -> Core ImperativeStatement
  expToFnBody x =
    do
      (s, r) <- impExp x
      pure $ s <+> ReturnStatement r

  impVectExp : {auto c : Ref Imps ImpSt} -> Vect n NamedCExp -> Core (ImperativeStatement, Vect n ImperativeExp)
  impVectExp args =
    do
      a <- traverseVect impExp args
      pure (concat (map fst a), map snd a)

  impListExp : {auto c : Ref Imps ImpSt} -> List NamedCExp -> Core (ImperativeStatement, List ImperativeExp)
  impListExp args =
    do
      a <- traverse impExp args
      pure (concat (map fst a), map snd a)

  impExp : {auto c : Ref Imps ImpSt} -> NamedCExp -> Core (ImperativeStatement, ImperativeExp)
  impExp (NmLocal fc n) = pure (DoNothing, IEVar n)
  impExp (NmRef fc n) = pure (DoNothing, IEVar n)
  impExp (NmLam fc n e) = pure (DoNothing, IELambda [n] !(expToFnBody e))
  impExp (NmApp fc x args) =
    do
      (s1, f) <- impExp x
      (s2, a) <- impListExp args
      pure (s1 <+> s2, IEApp f a)
  impExp (NmPrimVal fc c) = pure (DoNothing, IEConstant c)
  impExp (NmOp fc op args) =
    do
      (s, a) <- impVectExp args
      pure (s, IEPrimFn op a)
  impExp (NmConCase fc sc alts def) =
    do
      (s1, exp) <- impExp sc
      res <- genName
      swalts <- traverse (impConAlt res exp) alts
      swdef <- case def of
                Nothing => pure $ ErrorStatement $ "unhandled con case on " ++ show fc
                Just x =>
                  do
                    (sd, r) <- impExp x
                    pure $ sd <+> MutateStatement res r
      let switch = SwitchStatement (IEConstructorHead exp) swalts (Just swdef)
      pure (s1 <+> LetDecl res Nothing <+> switch, IEVar res)
  impExp (NmConstCase fc sc alts def) =
    do
      (s1, exp) <- impExp sc
      res <- genName
      swalts <- traverse (impConstAlt res) alts
      swdef <- case def of
                Nothing => pure $ ErrorStatement $ "unhandled const case on " ++ show fc
                Just x =>
                  do
                    (sd, r) <- impExp x
                    pure $ sd <+> MutateStatement res r
      let switch = SwitchStatement exp swalts (Just swdef)
      pure (s1 <+> LetDecl res Nothing <+> switch, IEVar res)
  impExp (NmExtPrim fc p args) =
    do
      (s, a) <- impListExp args
      pure (s, IEPrimFnExt p a)
  impExp (NmCon fc x tag args) =
    do
      (s, a) <- impListExp args
      pure (s, IEConstructor (impTag x tag) a)
  impExp (NmDelay fc t) =
    do
      (s, x) <- impExp t
      pure (s, IEDelay x)
  impExp (NmForce fc t) =
    do
      (s, x) <- impExp t
      pure (s, IEForce x)
  impExp (NmLet fc x val sc) =
    do
      (s1, v) <- impExp val
      (s2, sc_) <- impExp sc
      let decl  = if isNameUsed x sc then ConstDecl x v else EvalExpStatement v
      pure (s1 <+> decl <+> s2, sc_)
  impExp (NmErased fc) =
    pure (DoNothing, IENull)
  impExp (NmCrash fc msg) =
    pure (ErrorStatement msg, IENull)

  impTag : Name -> Maybe Int -> Either Int String
  impTag n Nothing = Right $ show n
  impTag n (Just i) = Left i

  impConAlt : {auto c : Ref Imps ImpSt} -> Name -> ImperativeExp -> NamedConAlt -> Core (ImperativeExp, ImperativeStatement)
  impConAlt res target (MkNConAlt n tag args exp) =
    do
      (s, r) <- impExp exp
      let nargs = length args
      let reps = zipWith (\i, n => (n, IEConstructorArg (cast i) target)) [1..nargs] args
      pure (IEConstructorTag (impTag n tag), replaceNamesExpS reps $ s <+> MutateStatement res r)

  impConstAlt : {auto c : Ref Imps ImpSt} -> Name -> NamedConstAlt -> Core (ImperativeExp, ImperativeStatement)
  impConstAlt res (MkNConstAlt c exp) =
    do
      (s, r) <- impExp exp
      pure (IEConstant c, s <+> MutateStatement res r)

getImp : {auto c : Ref Imps ImpSt} -> (Name, FC, NamedDef) -> Core ImperativeStatement
getImp (n, fc, MkNmFun args exp) =
  pure $ FunDecl fc n args !(expToFnBody exp)
getImp (n, fc, MkNmError exp) =
  throw $ (InternalError $ show exp)
getImp (n, fc, MkNmForeign cs args ret) =
  pure $ ForeignDecl n cs
getImp (n, fc, MkNmCon _ _ _) =
  pure DoNothing

export
compileToImperative : Ref Ctxt Defs -> ClosedTerm -> Core ImperativeStatement
compileToImperative c tm =
  do
    cdata <- getCompileData Cases tm
    let ndefs = namedDefs cdata
    let ctm = forget (mainExpr cdata)
    s <- newRef Imps (MkImpSt 0)
    compdefs <- traverse getImp (defsUsedByNamedCExp ctm ndefs)
    (s, main) <- impExp ctm
    pure $ concat compdefs <+> s <+> EvalExpStatement main -- <+> CommentStatement (show ndefs)
