module Compiler.ES.ImperativeAst

import Compiler.CompileExpr
import public Core.TT
import public Data.Vect
import public Data.List

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
                     | IEConstructorArg Int ImperativeExp -- constructor arg index starts at 1
                     | IEConstructor (Either Int String) (List ImperativeExp)
                     | IEDelay ImperativeExp
                     | IEForce ImperativeExp
                     | IENull

  public export
  data ImperativeStatement = DoNothing
                           | SeqStatement ImperativeStatement ImperativeStatement
                           | FunDecl FC Name (List Name) ImperativeStatement
                           | ForeignDecl FC Name (List String) (List CFType) CFType
                           | ReturnStatement ImperativeExp
                           | SwitchStatement ImperativeExp (List (ImperativeExp, ImperativeStatement)) (Maybe ImperativeStatement)
                           | LetDecl Name (Maybe ImperativeExp)
                           | ConstDecl Name ImperativeExp
                           | MutateStatement Name ImperativeExp
                           | ErrorStatement String
                           | EvalExpStatement ImperativeExp
                           | CommentStatement String
                           | ForEverLoop ImperativeStatement

public export
Semigroup ImperativeStatement where
  DoNothing <+> y = y
  x <+> DoNothing = x
  x <+> y = SeqStatement x y

public export
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
    show (ForeignDecl fc n path args ret) = "(ForeignDecl " ++ show n ++ " " ++ show path ++")"
    show (ReturnStatement x) = "(ReturnStatement " ++ show x ++ ")"
    show (SwitchStatement e alts d) = "(SwitchStatement " ++ show e ++ " " ++ show alts ++ " " ++ show d ++ ")"
    show (LetDecl n v) = "(LetDecl " ++ show n ++ " " ++ show v ++ ")"
    show (ConstDecl n v) = "(ConstDecl " ++ show n ++ " " ++ show v ++ ")"
    show (MutateStatement n v) = "(MutateStatement " ++ show n ++ " " ++ show v ++ ")"
    show (ErrorStatement s) = "(ErrorStatement " ++ s ++ ")"
    show (EvalExpStatement x) =  "(EvalExpStatement " ++ show x ++ ")"
    show (CommentStatement x) = "(CommentStatement " ++ show x ++ ")"
    show (ForEverLoop x) = "(ForEverLoop " ++ show x ++ ")"

mutual
  public export
  replaceExp : (ImperativeExp -> Maybe ImperativeExp) -> ImperativeExp -> ImperativeExp
  replaceExp rep x@(IEVar n) =
    case rep x of
      Just z => z
      Nothing => x
  replaceExp rep x@(IELambda args body) =
    case rep x of
      Just z => z
      Nothing => IELambda args $ replaceExpS rep body
  replaceExp rep x@(IEApp f args) =
    case rep x of
      Just z => z
      Nothing => IEApp (replaceExp rep f) (replaceExp rep <$> args)
  replaceExp rep x@(IEConstant c) =
    case rep x of
      Just z => z
      Nothing => x
  replaceExp rep x@(IEPrimFn f args) =
    case rep x of
      Just z => z
      Nothing => IEPrimFn f (replaceExp rep <$> args)
  replaceExp rep x@(IEPrimFnExt f args) =
    case rep x of
      Just z => z
      Nothing => IEPrimFnExt f (replaceExp rep <$> args)
  replaceExp rep x@(IEConstructorHead e) =
    case rep x of
      Just z => z
      Nothing => IEConstructorHead $ replaceExp rep e
  replaceExp rep x@(IEConstructorTag i) =
    case rep x of
      Just z => z
      Nothing => x
  replaceExp rep x@(IEConstructorArg i e) =
    case rep x of
      Just z => z
      Nothing => IEConstructorArg i (replaceExp rep e)
  replaceExp rep x@(IEConstructor t args) =
    case rep x of
      Just z => z
      Nothing => IEConstructor t (replaceExp rep <$> args)
  replaceExp rep x@(IEDelay e) =
    case rep x of
      Just z => z
      Nothing => IEDelay $ replaceExp rep e
  replaceExp rep x@(IEForce e) =
    case rep x of
      Just z => z
      Nothing => IEForce $ replaceExp rep e
  replaceExp rep x@IENull =
    case rep x of
      Just z => z
      Nothing => x

  public export
  replaceExpS : (ImperativeExp -> Maybe ImperativeExp) -> ImperativeStatement -> ImperativeStatement
  replaceExpS rep DoNothing =
    DoNothing
  replaceExpS rep (SeqStatement x y) =
    SeqStatement (replaceExpS rep x) (replaceExpS rep y)
  replaceExpS rep (FunDecl fc n args body) =
    FunDecl fc n args $ replaceExpS rep body
  replaceExpS reps decl@(ForeignDecl fc n path args ret) =
    decl
  replaceExpS rep (ReturnStatement e) =
    ReturnStatement $ replaceExp rep e
  replaceExpS rep (SwitchStatement s alts def) =
    let s_    = replaceExp rep s
        alts_ = (\(e,b) => (replaceExp rep e, replaceExpS rep b)) <$> alts
        def_  = replaceExpS rep <$> def
    in SwitchStatement s_ alts_ def_
  replaceExpS rep (LetDecl n v) =
    LetDecl n $ replaceExp rep <$> v
  replaceExpS rep (ConstDecl n v) =
    ConstDecl n $ replaceExp rep v
  replaceExpS rep (MutateStatement n v) =
    MutateStatement n $ replaceExp rep v
  replaceExpS rep (ErrorStatement s) =
    ErrorStatement s
  replaceExpS rep (EvalExpStatement x) =
    EvalExpStatement $ replaceExp rep x
  replaceExpS rep (CommentStatement x) =
    CommentStatement x
  replaceExpS rep (ForEverLoop x) =
    ForEverLoop $ replaceExpS rep x


rep : List (Name, ImperativeExp) -> ImperativeExp -> Maybe ImperativeExp
rep reps (IEVar n) =
  lookup n reps
rep _ _ = Nothing

public export
replaceNamesExpS : List (Name, ImperativeExp) -> ImperativeStatement -> ImperativeStatement
replaceNamesExpS reps x =
  replaceExpS (rep reps) x

public export
replaceNamesExp : List (Name, ImperativeExp) -> ImperativeExp -> ImperativeExp
replaceNamesExp reps x =
  replaceExp (rep reps) x
