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
                     | IEConstructorArg Int ImperativeExp
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

  public export
  replaceNamesExpS : List (Name, ImperativeExp) -> ImperativeStatement -> ImperativeStatement
  replaceNamesExpS reps DoNothing =
    DoNothing
  replaceNamesExpS reps (SeqStatement x y) =
    SeqStatement (replaceNamesExpS reps x) (replaceNamesExpS reps y)
  replaceNamesExpS reps (FunDecl fc n args body) =
    FunDecl fc n args $ replaceNamesExpS reps body
  replaceNamesExpS reps decl@(ForeignDecl fc n path args ret) =
    decl
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
  replaceNamesExpS reps (ForEverLoop x) =
    ForEverLoop $ replaceNamesExpS reps x
