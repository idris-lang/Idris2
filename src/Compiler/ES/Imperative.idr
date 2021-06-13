||| This module is responsible for compiling an
||| Idris2 `ClosedTerm` to a pair of `ImperativeStatement`s,
||| one of which corresponds to a sequence of toplevel
||| definitions, the other being the program's main entry
||| point.
module Compiler.ES.Imperative

import public Compiler.ES.ImperativeAst

import Data.List

import Compiler.Common
import Compiler.CompileExpr

import public Core.Context

import Compiler.ES.RemoveUnused
import Compiler.ES.TailRec

%default covering

mutual
  isNameUsed : Name -> NamedCExp -> Bool
  isNameUsed name (NmLocal fc n) = n == name
  isNameUsed name (NmRef fc n) = n == name
  isNameUsed name (NmLam fc n e) = isNameUsed name e
  isNameUsed name (NmApp fc x args)
    = isNameUsed name x || any (isNameUsed name) args
  isNameUsed name (NmPrimVal fc c) = False
  isNameUsed name (NmOp fc op args) = any (isNameUsed name) args
  isNameUsed name (NmConCase fc sc alts def)
    = isNameUsed name sc
    || any (isNameUsedConAlt name) alts
    || maybe False (isNameUsed name) def
  isNameUsed name (NmConstCase fc sc alts def)
    = isNameUsed name sc
    || any (isNameUsedConstAlt name) alts
    || maybe False (isNameUsed name) def
  isNameUsed name (NmExtPrim fc p args) = any (isNameUsed name) args
  isNameUsed name (NmCon fc x _ t args) = any (isNameUsed name) args
  isNameUsed name (NmDelay fc _ t) = isNameUsed name t
  isNameUsed name (NmForce fc _ t) = isNameUsed name t
  isNameUsed name (NmLet fc x val sc) =
    if x == name then isNameUsed name val
      else isNameUsed name val || isNameUsed name sc
  isNameUsed name (NmErased fc) = False
  isNameUsed name (NmCrash fc msg) = False

  isNameUsedConAlt : Name -> NamedConAlt -> Bool
  isNameUsedConAlt name (MkNConAlt n _ t args exp) = isNameUsed name exp

  isNameUsedConstAlt : Name -> NamedConstAlt -> Bool
  isNameUsedConstAlt name (MkNConstAlt c exp) = isNameUsed name exp

data Imps : Type where

record ImpSt where
  constructor MkImpSt
  nextName : Int

genName : {auto c : Ref Imps ImpSt} -> Core Name
genName =
  do s <- get Imps
     let i = nextName s
     put Imps (record { nextName = i + 1 } s)
     pure $ MN "imp_gen" i

-- Processing an Idris2 expression results in
-- an `ImperativeStatement` (since this is a monoid,
-- this might actually be many statements) of utility
-- functions and intermediary vars and results, and
-- a final imperative expression, calculating a result
-- from the related statement(s). These
-- are then converted to JS code.
--
-- The boolean flag indicates, whether the two parts
-- should be returned as a pair for further
-- processing, or should be converted
-- to a single statement (in which case, the final
-- expression is converted to a `return` statement).
ImperativeResult : (toReturn : Bool) -> Type
ImperativeResult True  = ImperativeStatement
ImperativeResult False = (ImperativeStatement, ImperativeExp)

-- when invoking `impExp`, in some cases we always
-- generate a pair (statements plus related final
-- expression). In such a case, this function converts
-- the statement to the correct result type as indicated
-- by `toReturn`.
pairToReturn :  (toReturn : Bool)
             -> (ImperativeStatement, ImperativeExp)
             -> (ImperativeResult toReturn)
pairToReturn False (s, e) = (s, e)
pairToReturn True (s, e)  = s <+> ReturnStatement e

-- when invoking `impExp`, in some cases we
-- generate just an expression.
-- In such a case, this function converts
-- the expression to the correct result type as indicated
-- by `toReturn`.
expToReturn :  (toReturn : Bool)
            -> ImperativeExp
            -> (ImperativeResult toReturn)
expToReturn False e = (DoNothing, e)
expToReturn True e  = ReturnStatement e

impTag : Name -> Maybe Int -> Either Int String
impTag n Nothing = Right $ show n
impTag n (Just i) = Left i

-- memoize an intermediary result in a `let` binding.
-- doesn't do anything if `exp` is a variable, constant
-- or undefined.
memoExp : {auto c : Ref Imps ImpSt}
        -> (exp : ImperativeExp)
        -> Core (ImperativeStatement, ImperativeExp)
memoExp e@(IEVar _)      = pure (neutral, e)
memoExp e@(IEConstant _) = pure (neutral, e)
memoExp IENull           = pure (neutral, IENull)
memoExp e                = map (\n =>(LetDecl n $ Just e, IEVar n)) genName

mutual
  -- converts primOps arguments to a set of
  -- statements plus a corresponding vect of expressions
  impVectExp :  {auto c : Ref Imps ImpSt}
             -> Vect n NamedCExp
             -> Core (ImperativeStatement, Vect n ImperativeExp)
  impVectExp args =
    do a <- traverseVect (impExp False) args
       pure (concatMap fst a, map snd a)

  -- converts function arguments to a set of
  -- statements plus a corresponding list of expressions
  impListExp :  {auto c : Ref Imps ImpSt}
             -> List NamedCExp
             -> Core (ImperativeStatement, List ImperativeExp)
  impListExp args =
    do a <- traverse (impExp False) args
       pure (concatMap fst a, map snd a)

  impExp :  {auto c : Ref Imps ImpSt}
         -> (toReturn : Bool)
         -> NamedCExp
         -> Core (ImperativeResult toReturn)
  -- convert local names to vars
  impExp toReturn (NmLocal fc n) =
    pure . expToReturn toReturn $ IEVar n

  impExp toReturn (NmRef fc n) =
    pure . expToReturn toReturn $ IEVar n

  -- TODO: right now, nested lambda expressions are curried
  -- (or are they?).
  -- It might be more efficient (and more readable!) to uncurry
  -- these, at least in the most simple cases.
  impExp toReturn (NmLam fc n e) =
    pure . expToReturn toReturn $ IELambda [n] !(impExp True e)

  -- Function application: Statements for the
  -- implementation of the function and the arguments are
  -- generated separately and concatenated.
  impExp toReturn (NmApp fc x args) =
    do (s1, f) <- impExp False x
       (s2, a) <- impListExp args
       pure $ pairToReturn toReturn (s1 <+> s2, IEApp f a)

  -- primitive values
  impExp toReturn (NmPrimVal fc c) =
    pure . expToReturn toReturn $ IEConstant c

  -- primitive operations
  impExp toReturn (NmOp fc op args) =
    do (s, a) <- impVectExp args
       pure $ pairToReturn toReturn (s, IEPrimFn op a)

  -- a pattern match on a constructor
  -- is converted to a switch statement in JS.
  --
  -- TODO: We should treat record constructors
  --       separately, to avoid the unnecessary
  --       switch
  --
  -- ```
  -- s1
  -- let res;
  -- switch(exp.h) {
  --   alternatives
  --   default (if any)
  -- }
  -- res;
  -- ```
  impExp False (NmConCase fc sc alts def) =
    do (s1, exp)  <- impExp False sc
       (s2, exp2) <- memoExp exp
       res    <- genName
       swalts <- traverse (impConAltFalse res exp2) alts
       swdef  <- case def of
                   Nothing => pure $ ErrorStatement $ "unhandled con case on " ++ show fc
                   Just x =>
                    do (sd, r) <- impExp False x
                       pure $ sd <+> MutateStatement res r
       let switch = SwitchStatement (IEConstructorHead exp2) swalts (Just swdef)
       pure (s1 <+> s2 <+> LetDecl res Nothing <+> switch, IEVar res)

  -- like `impExp False NmConCase`, but we return directly without
  -- a local let binding
  impExp True (NmConCase fc sc alts def) =
    do (s1, exp) <- impExp False sc
       (s2, exp2) <- memoExp exp
       swalts <- traverse (impConAltTrue exp2) alts
       swdef <- case def of
                 Nothing => pure $ ErrorStatement $ "unhandled con case on " ++ show fc
                 Just x => impExp True x
       let switch = SwitchStatement (IEConstructorHead exp2) swalts (Just swdef)
       pure (s1 <+> s2 <+> switch)

  -- a case statement (pattern match on a constant)
  -- is converted to a switch statement in JS.
  -- the distinction between `impExp False` and
  -- `impExp True` is the same as for constructor matches
  impExp False (NmConstCase fc sc alts def) =
    do (s1, exp) <- impExp False sc
       res <- genName
       swalts <- traverse (impConstAltFalse res) alts
       swdef <- case def of
                  Nothing => pure $ ErrorStatement $ "unhandled const case on " ++ show fc
                  Just x =>
                    do
                      (sd, r) <- impExp False x
                      pure $ sd <+> MutateStatement res r
       let switch = SwitchStatement exp swalts (Just swdef)
       pure (s1 <+> LetDecl res Nothing <+> switch, IEVar res)

  impExp True (NmConstCase fc sc alts def) =
    do (s1, exp) <- impExp False sc
       swalts <- traverse impConstAltTrue alts
       swdef <- case def of
                 Nothing => pure $ ErrorStatement $ "unhandled const case on " ++ show fc
                 Just x => impExp True x
       let switch = SwitchStatement exp swalts (Just swdef)
       pure $ s1 <+> switch

  -- coversion of primitive external functions like
  -- `prim__newIORef`
  impExp toReturn (NmExtPrim fc p args) =
    do (s, a) <- impListExp args
       pure $ pairToReturn toReturn (s, IEPrimFnExt p a)

  -- A saturated constructor
  -- TODO: Use ConInfo
  impExp toReturn (NmCon fc x _ tag args) =
    do (s, a) <- impListExp args
       pure $ pairToReturn toReturn
         (s, IEConstructor (impTag x tag) a)

  -- a delayed computation
  impExp toReturn (NmDelay fc _ t) =
    do (s, x) <- impExp False t
       pure $ pairToReturn toReturn (s, IEDelay x)

  -- a forced computation
  impExp toReturn (NmForce fc _ t) =
    do (s, x) <- impExp False t
       pure $ pairToReturn toReturn (s, IEForce x)

  -- a let statement of the form
  -- ```idris
  -- let name = expr1
  --  in expr2
  --
  -- ```
  -- is converted to
  --
  -- ```javascript
  -- expr1_statements;
  -- const name_ = expr1_expr;
  -- expr2_statements;
  -- expr2_expr;
  -- ```
  -- where `name_` is a newly generated name, which
  -- is replaced in `expr2`.
  --
  -- if `name` is not used in `expr2`, this is
  -- simplified to
  --
  -- ```javascript
  -- expr1_statements;
  -- expr1_expr; -- evaluation of expr1!
  -- expr2_statements;
  -- expr2_expr;
  -- ```
  -- TODO: Is it necessary to generate a new name
  -- here, or is this already handled by Idris itself?
  impExp toReturn (NmLet fc x val sc) =
    do (s1, v)   <- impExp False val
       (s2, sc_) <- impExp False sc
       if isNameUsed x sc
         then do
           x_ <- genName
           let reps = [(x, IEVar x_)]
           let s2_  = replaceNamesExpS reps s2
           let sc__ = replaceNamesExp reps sc_
           let decl = ConstDecl x_ v
           pure $ pairToReturn toReturn (s1 <+> decl <+> s2_, sc__)
         else do
           let decl = EvalExpStatement v
           pure $ pairToReturn toReturn (s1 <+> decl <+> s2, sc_)

  -- an erased argument is converted to `undefined`
  impExp toReturn (NmErased fc) =
    pure . expToReturn toReturn $ IENull

  -- an error is converted to a `throw new Error`
  -- statement. It's result is `undefined` (`IENull`).
  impExp toReturn (NmCrash fc msg) =
    pure $ pairToReturn toReturn (ErrorStatement msg, IENull)

  -- a single alternative in a case statement.
  -- In JS, this will be a single alternative of
  -- a switch statement.
  -- TODO: Use ConInfo
  --
  -- @ res : name of the local var (from a `let` statement)
  --         to which the result should be assigned (if any)
  -- @ target : The value against which to match
  -- @ con : The constructor to use
  impConAltFalse :  {auto c : Ref Imps ImpSt}
                 -> (res : Name)
                 -> (target : ImperativeExp)
                 -> (con : NamedConAlt)
                 -> Core (ImperativeExp, ImperativeStatement)
  impConAltFalse res target (MkNConAlt n _ tag args exp) =
    do (s, r) <- impExp False exp
       (tgts,tgte) <- memoExp target
       let nargs = length args
       let reps = zipWith (\i, n => (n, IEConstructorArg (cast i) tgte))
                          [1..nargs]
                          args
       pure ( IEConstructorTag (impTag n tag)
            , tgts <+> (replaceNamesExpS reps $ s <+> MutateStatement res r)
            )

  impConAltTrue :  {auto c : Ref Imps ImpSt}
                -> (target : ImperativeExp)
                -> (con : NamedConAlt)
                -> Core (ImperativeExp, ImperativeStatement)
  impConAltTrue target (MkNConAlt n _ tag args exp) =
    do s <- impExp True exp
       (tgts,tgte) <- memoExp target
       let nargs = length args
       let reps = zipWith (\i, n => (n, IEConstructorArg (cast i) tgte))
                          [1..nargs]
                          args
       pure ( IEConstructorTag (impTag n tag), tgts <+> replaceNamesExpS reps s)

  impConstAltFalse :  {auto c : Ref Imps ImpSt}
                   -> Name
                   -> NamedConstAlt
                   -> Core (ImperativeExp, ImperativeStatement)
  impConstAltFalse res (MkNConstAlt c exp) =
    do (s, r) <- impExp False exp
       pure (IEConstant c, s <+> MutateStatement res r)

  impConstAltTrue :  {auto c : Ref Imps ImpSt}
                  -> NamedConstAlt
                  -> Core (ImperativeExp, ImperativeStatement)
  impConstAltTrue (MkNConstAlt c exp) =
    do s <- impExp True exp
       pure (IEConstant c, s)

-- generate an `ImperativeStatement` from the
-- given named definition
getImp :  {auto c : Ref Imps ImpSt}
       -> (Name, FC, NamedDef)
       -> Core ImperativeStatement
getImp (n, fc, MkNmFun args exp) =
  pure $ FunDecl fc n args !(impExp True exp)
getImp (n, fc, MkNmError exp) =
  throw $ (InternalError $ show exp)
getImp (n, fc, MkNmForeign cs args ret) =
  pure $ ForeignDecl fc n cs args ret
getImp (n, fc, MkNmCon _ _ _) =
  pure DoNothing

||| Compiles a `ClosedTerm` to a pair of statements,
||| the first corresponding to a list of toplevel definitions
||| the other being the program's main entry point.
|||
||| Toplevel definitions defined in the given `ClosedTerm`
||| are only included if they are (transitively) being
||| invoked by the main function.
|||
||| In addition, toplevel definitions are tail call optimized
||| (see module `Compiler.ES.TailRec`).
export
compileToImperative :  Ref Ctxt Defs
                    -> ClosedTerm
                    -> Core (ImperativeStatement, ImperativeStatement)
compileToImperative c tm =
  do -- generate the named definitions and main expression
     -- from the `ClosedTerm`
     cdata <- getCompileData False Cases tm

     -- list of named definitions
     let ndefs = namedDefs cdata

     -- main expression
     let ctm = forget (mainExpr cdata)

     ref <- newRef Imps (MkImpSt 0)

     -- list of toplevel definitions (only those necessary
     -- to implement the main expression)
     lst_defs <- traverse getImp (defsUsedByNamedCExp ctm ndefs)

     let defs = concat lst_defs

     -- tail rec optimited definitions
     defs_optim <- tailRecOptim defs

     -- main expression and statements necessary to
     -- implement main's body
     (s, main) <- impExp False ctm
     pure $ (defs_optim, s <+> EvalExpStatement main)
