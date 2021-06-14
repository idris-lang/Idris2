||| ASTs representing imperative ES (= ECMAScript)
||| expressions and statements.
||| These are converted to ES code in module `Compiler.ES.ES`.
||| They are generated from `Term []`s in
||| module `Compiler.ES.Imperative`.
module Compiler.ES.ImperativeAst

import Compiler.CompileExpr
import public Core.TT
import public Data.Vect
import public Data.List

%default covering

mutual
  ||| A tree representing an ES expression.
  |||
  ||| This is converted to ES code in function
  ||| `Compiler.ES.ES.impExp2es`.
  public export
  data ImperativeExp : Type where
    ||| A variable of the given name
    IEVar : (name : Name) -> ImperativeExp

    ||| A lambda expression : `(args) => { body }`
    IELambda :  (args : List Name)
             -> (body : ImperativeStatement)
             -> ImperativeExp

    ||| Function application : `lhs(args)`
    IEApp :  (lhs  : ImperativeExp)
          -> (args : List ImperativeExp)
          -> ImperativeExp

    ||| A (primitive) constant
    IEConstant : (value : Constant) -> ImperativeExp

    ||| A primitive function. This will be converted to
    ||| ES code in `Compiler.ES.ES.jsOp`.
    IEPrimFn :  (function : PrimFn arity)
             -> (args : Vect arity ImperativeExp)
             -> ImperativeExp

    ||| A primitive external function. Example `prim__newIORef`
    IEPrimFnExt :  (function : Name)
                -> (args : List ImperativeExp)
                -> ImperativeExp

    ||| Calls `object.h` on the JS object built by `object`
    ||| This is used to extract the constructor, which
    ||| this specific object represents.
    IEConstructorHead : (object : ImperativeExp) -> ImperativeExp

    ||| Tag representing either a data constructor (in that case
    ||| an integer is used as its index) or a type constructor
    ||| (these come up when pattern matching on types).
    IEConstructorTag : (tag : Either Int String) -> ImperativeExp

    ||| Argument of a data constructor applied to the given JS object.
    ||| The arg index starts at 1.
    |||
    ||| Example: `object.a3`
    IEConstructorArg :  (index : Int)
                     -> (object : ImperativeExp)
                     -> ImperativeExp

    ||| Creates a JS object using the given constructor
    ||| tag and arguments. The corresponding values are
    ||| extracted using `IEConstructorTag` and `IEConstructorArg`.
    IEConstructor :  (tag  : Either Int String)
                  -> (args : List ImperativeExp)
                  -> ImperativeExp

    ||| A delayed calculation coming either from a `Lazy`
    ||| or infinite (`Inf`) value.
    |||
    ||| In the JS backends, these are wrapped zero-argument lambdas:
    ||| `(() => expr)`.
    IEDelay : (expr : ImperativeExp) -> ImperativeExp

    ||| Forces the evaluation of a delayed (`Lazy` or `Inf`)
    ||| value.
    |||
    ||| In the JS backends, these just invoke the corresponding
    ||| zero-argument lambdas:
    ||| `expr()`.
    IEForce : (expr : ImperativeExp) -> ImperativeExp

    ||| This is converted to `undefined`.
    |||
    ||| TODO: This should be renamed to `IEUndefined` in
    |||       order not to be confused with the JS constant
    |||       `null`.
    IENull : ImperativeExp

  ||| A tree of ES statements.
  |||
  ||| This is converted to ES code in `Compiler.ES.imperative2es`.
  public export
  data ImperativeStatement : Type where
    ||| This is converted to the empty string.
    DoNothing : ImperativeStatement

    ||| A sequence of statements. These will be processed
    ||| individually and separated by a line break.
    SeqStatement :  (fstStmt : ImperativeStatement)
                 -> (sndStmt : ImperativeStatement)
                 -> ImperativeStatement

    ||| A function declaration. This will be converted
    ||| to a declaration of the following form:
    |||
    ||| ```
    ||| function funName(args){ -- fc
    |||   body
    ||| }
    ||| ```
    FunDecl :  (fc : FC)
            -> (funName : Name)
            -> (args : List Name)
            -> (body : ImperativeStatement)
            -> ImperativeStatement

    ||| An FFI declaration
    |||
    ||| @ ffiImpls : List of implementation strings.
    |||              `Compiler.ES.ES.foreignDecl`
    |||              will try to lookup a valid codegen prefix like "node"
    |||              or "javascript" in each of these and return the
    |||              remainder as the actual ES code in case of a success.
    |||
    ||| The argtypes and returnType will be ignored when generating
    ||| ES code.
    ForeignDecl :  (fc : FC)
                -> (funName : Name)
                -> (ffiImpls : List String)
                -> (argTypes : List CFType)
                -> (returnType : CFType)
                -> ImperativeStatement

    ||| A `return` statement. Example: `return body;`
    ReturnStatement : (body : ImperativeExp) -> ImperativeStatement

    ||| A `switch` statement of the form
    |||
    ||| ```
    ||| switch(expr) {
    |||  case altExp1 : {
    |||    altImpl1
    |||    break;
    |||  }
    |||  case altExp2 : {
    |||    altImpl2
    |||    break;
    |||  }
    |||  default:
    |||    deflt
    ||| }
    ||| ```
    SwitchStatement :  (expr  : ImperativeExp)
                    -> (alts  : List (ImperativeExp, ImperativeStatement))
                    -> (deflt : Maybe ImperativeStatement)
                    -> ImperativeStatement

    ||| A `let` statement with an optional value
    ||| This is converted to `let name;` if `value`
    ||| is `Nothing` and to `let name = expr;` if
    ||| `value` is `Just expr`.
    LetDecl :  (name  : Name)
            -> (value : Maybe ImperativeExp)
            -> ImperativeStatement

    ||| A `const` declaration.
    ||| This is converted to `const name = expr;`.
    ConstDecl :  (name : Name)
              -> (expr :  ImperativeExp)
              -> ImperativeStatement

    ||| Assigns the given expression to the variable
    ||| of the given name: `name = expr;`.
    MutateStatement :  (name : Name)
                    -> (expr : ImperativeExp)
                    -> ImperativeStatement

    ||| Throws an error with the given message:
    ||| `throw new Error(msg);`.
    ErrorStatement : (msg : String) -> ImperativeStatement

    ||| Evaluates the given expression (by ending the corresponding
    ||| ES code with a semicolon):
    ||| `expr;`.
    EvalExpStatement : (expr : ImperativeExp) -> ImperativeStatement

    ||| Adds the given String as a comment
    ||| `/*comment*/`.
    CommentStatement : (comment : String) -> ImperativeStatement

    ||| Runs the given statement 'forever':
    |||
    ||| ```
    ||| while(true){
    |||  body
    ||| }
    ||| ```
    ForEverLoop : (body : ImperativeStatement) -> ImperativeStatement

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
  ||| Iteratively replaces expressions using
  ||| the given function. This is mainly used for
  ||| replacing variables according to their name as
  ||| in `replaceNamesExp`.
  public export
  replaceExp :  (ImperativeExp -> Maybe ImperativeExp)
             -> ImperativeExp
             -> ImperativeExp
  replaceExp rep x =
    case rep x of
      Just z  => z
      Nothing =>
        case x of
          IEVar _              => x
          IELambda args body   => IELambda args $ replaceExpS rep body
          IEApp f args         => IEApp (replaceExp rep f)
                                        (replaceExp rep <$> args)
          IEConstant _         => x
          IEPrimFn f args      => IEPrimFn f (replaceExp rep <$> args)
          IEPrimFnExt f args   => IEPrimFnExt f (replaceExp rep <$> args)
          IEConstructorHead e  => IEConstructorHead $ replaceExp rep e
          IEConstructorTag _   => x
          IEConstructorArg i e => IEConstructorArg i (replaceExp rep e)
          IEConstructor t args => IEConstructor t (replaceExp rep <$> args)
          IEDelay e            => IEDelay $ replaceExp rep e
          IEForce e            => IEForce $ replaceExp rep e
          IENull               => x

  ||| Iteratively replaces expressions using
  ||| the given function. This is mainly used for
  ||| replacing variables according to their name as
  ||| in `replaceNamesExpS`.
  public export
  replaceExpS :  (ImperativeExp -> Maybe ImperativeExp)
              -> ImperativeStatement
              -> ImperativeStatement
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


rep :  List (Name, ImperativeExp)
    -> ImperativeExp
    -> Maybe ImperativeExp
rep reps (IEVar n) = lookup n reps
rep _    _         = Nothing

||| Replaces all occurences of the names in the
||| assoc list with the corresponding expression.
public export
replaceNamesExpS :  List (Name, ImperativeExp)
                 -> ImperativeStatement
                 -> ImperativeStatement
replaceNamesExpS reps x =
  replaceExpS (rep reps) x

||| Replaces all occurences of the names in the
||| assoc list with the corresponding expression.
public export
replaceNamesExp :  List (Name, ImperativeExp)
                -> ImperativeExp
                -> ImperativeExp
replaceNamesExp reps x =
  replaceExp (rep reps) x
