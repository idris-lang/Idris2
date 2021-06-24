||| Rules:
|||   * a function (toplevel or lambda) always ends in a
|||     return statement (or an error)
|||   * intermediare statements are either constants (const values)
|||     or switch statements, which end in an assignment to
|||     a previously declared but unassigned variable.
module Compiler.ES.Ast

import Core.CompileExpr
import Core.Context
import Compiler.Common
import Data.Nat

import Data.Vect

%default total

||| A variable in a toplevel function definition
|||
||| Including projections here facilitates inlining them
||| in argument lists.
public export
data Var = VName Name -- a name
         | VLoc  Int  -- a local variable
         | VRef  Int  -- a (mangled) toplevel function

public export
data Minimal = MVar Var | MProjection Nat Minimal

--------------------------------------------------------------------------------
--          Expressions
--------------------------------------------------------------------------------

||| The target of a statement. `RVal` means the
||| result of the final expression will be returned as
||| the current function's result, while `TN n` is a
||| variable to which the result of the final expression will
||| be assigned.
public export
data Effect = Returns | ErrorWithout Var

mutual
  ||| An expression in a function definition.
  public export
  data Exp : Type where
    ||| A variable or projection. Minimal expressions
    ||| will always be inlined unless explicitly bound
    ||| in a `let` expression.
    EMinimal  : Minimal -> Exp

    ||| Lambda expression
    |||
    ||| An empty argument list represents a delayed computation
    ELam      : List Var -> Block Returns -> Exp

    ||| Function application.
    |||
    ||| In case of a zero-argument list, we might also be
    ||| dealing with forcing a delayed computation.
    EApp      : Exp -> List Exp -> Exp

    ||| Saturated construtor application
    ECon      : (tag : Either Int Name) -> ConInfo -> List Exp -> Exp

    ||| Primitive operation
    EOp       : {0 arity : Nat} -> PrimFn arity -> Vect arity Exp -> Exp

    ||| Externally define primitive operation
    EExtPrim  : Name -> List Exp -> Exp

    ||| A constant primitive
    EPrimVal  : Constant -> Exp

    ||| An erased value.
    EErased   : Exp

  ||| An imperative statement in a function definition.
  |||
  ||| This is indexed over the target, to which the
  ||| final expression of the statement will be assigned.
  ||| This allows us to keep track of where we are headed
  ||| to. A `Target` of `Nothing` means that the result of
  ||| the statement is `undefined`: The assignment of
  ||| a
  |||
  ||| For statements lifted to the outer scope from
  ||| an argument list, this will be the local variable,
  ||| to which the argument will be assigned. Same goes
  ||| for local variables from let bindings.
  |||
  ||| For statements producing the result of a function,
  ||| `target` will be `RVal`.
  |||
  ||| The advantage of this design is the following:
  ||| We can prove at the type level that all branches
  ||| of a switch statment will eventually assign their
  ||| result to the same target.
  public export
  data Stmt : (effect : Maybe Effect) -> Type where
    ||| Returns the given single line expression.
    Return      : Exp -> Stmt (Just Returns)

    ||| Introduces a new constant by assigning the result
    ||| of a single expression to the given variable.
    Const      : (v : Var) -> Exp -> Stmt Nothing

    ||| Assigns and expression to the given variable. This
    ||| will result in an error, if the variable has not
    ||| yet been declared.
    Assign     : (v : Var) -> Exp -> Stmt (Just $ ErrorWithout v)

    ||| Declares (but does not yet assign) a new (mutable)
    ||| variable.
    Declare    : (v : Var) -> Stmt (Just $ ErrorWithout v) -> Stmt Nothing

    ||| Switch statement from a pattern matching on
    ||| data constructors. The result of each branch
    ||| will be assigned to the given target.
    |||
    ||| The scrutinee has already been lifted to
    ||| the outer scope to make sure it is only
    ||| evaluated once.
    ConSwitch   :  (e         : Effect)
                -> (scrutinee : Minimal)
                -> (alts      : List $ EConAlt e)
                -> (def       : Maybe $ Block e)
                -> Stmt (Just e)

    ||| Switch statement from a pattern matching on
    ||| a constant. The result of each branch
    ||| will be assigned to the given target.
    ConstSwitch :  (e         : Effect)
                -> (scrutinee : Exp)
                -> (alts      : List $ EConstAlt e)
                -> (def       : Maybe $ Block e)
                -> Stmt (Just e)

    ||| A run time exception.
    Error       : {0 any : _} -> String -> Stmt any

  ||| A code block consisting of one or more
  ||| imperative statements. This is indexed over
  ||| the target to which the final expression will
  ||| be assigned.
  public export
  data Block : (e : Effect) -> Type where
    Result     : Stmt (Just e) -> Block e
    (::)       : Stmt Nothing  -> Block e -> Block e

  ||| Single branch in a pattern match on data or
  ||| type constructors.
  public export
  record EConAlt (e : Effect) where
    constructor MkEConAlt
    tag     : Either Int Name
    conInfo : ConInfo
    body    : Block e

  ||| Single branch in a pattern match on a constant
  public export
  record EConstAlt (e : Effect) where
    constructor MkEConstAlt
    constant : Constant
    body     : Block e

export
toMinimal : Exp -> Maybe Minimal
toMinimal (EMinimal v) = Just v
toMinimal _            = Nothing

export
prepend : List (Stmt Nothing) -> Block e -> Block e
prepend []       b = b
prepend (h :: t) b = h :: prepend t b

export total
declare : {v : _} -> Block (ErrorWithout v) -> List (Stmt Nothing)
declare (Result (Assign v y))            = [Const v y]
declare (Result c@(ConSwitch _ _ _ _))   = [Declare v c]
declare (Result c@(ConstSwitch _ _ _ _)) = [Declare v c]
declare (Result (Error x))               = [Error x]
declare (x :: y)                         = x :: declare y
