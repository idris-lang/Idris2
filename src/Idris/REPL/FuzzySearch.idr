module Idris.REPL.FuzzySearch

import Core.Context
import Core.Metadata
import Core.TT
import Core.Unify

import Idris.Doc.String
import Idris.IDEMode.Commands
import Idris.Pretty
import Idris.Syntax

import public Idris.REPL.Common

import Data.List
import Data.Maybe
import Data.String
import Libraries.Data.List.Extra
import Libraries.Data.String.Extra
import Libraries.Data.WithDefault

%default covering

export
fuzzySearch : {auto c : Ref Ctxt Defs}
           -> {auto s : Ref Syn SyntaxInfo}
           -> {auto o : Ref ROpts REPLOpts}
           -> PTerm
           -> Core REPLResult
fuzzySearch expr = do
  let Just (neg, pos) = parseExpr expr
    | _ => pure (REPLError ("Bad expression, expected"
                       <++> code "B"
                       <++> "or"
                       <++> code "_ -> B"
                       <++> "or"
                       <++> code "A -> B"
                       <+> ", where"
                       <++> code "A"
                       <++> "and"
                       <++> code "B"
                       <++> "are spines of global names"))
  defs <- branch
  let curr = currentNS defs
  let ctxt = gamma defs
  filteredDefs <-
    do names   <- allNames ctxt
       defs    <- traverse (flip lookupCtxtExact ctxt) names
       let defs = flip mapMaybe defs $ \ md =>
                      do d <- md
                         guard (visibleIn curr (fullname d) (collapseDefault $ visibility d))
                         guard (isJust $ userNameRoot (fullname d))
                         pure d
       allDefs <- traverse (resolved ctxt) defs
       filterM (predicate neg pos) allDefs
  put Ctxt defs
  doc <- traverse (docsOrSignature EmptyFC) $ fullname <$> filteredDefs
  pure $ PrintedDoc $ vsep doc
 where

  data NameOrConst = AName Name
                   | APrimType PrimType
                   | AType

  eqConst : (x, y : NameOrConst) -> Bool
  eqConst (APrimType x) (APrimType y) = x == y
  eqConst AType         AType         = True
  eqConst _             _             = False -- names equality is irrelevant

  parseNameOrConst : PTerm -> Maybe NameOrConst
  parseNameOrConst (PRef _ n)               = Just (AName n)
  parseNameOrConst (PPrimVal _ $ PrT t)     = Just (APrimType t)
  parseNameOrConst (PType _)                = Just AType
  parseNameOrConst _                        = Nothing

  parseExpr' : PTerm -> Maybe (List NameOrConst)
  parseExpr' (PApp _ f x) =
    [| parseNameOrConst x :: parseExpr' f |]
  parseExpr' x = (:: []) <$> parseNameOrConst x

  parseExpr : PTerm -> Maybe (List NameOrConst, List NameOrConst)
  parseExpr (PPi _ _ _ _ a (PImplicit _)) = do
    a' <- parseExpr' a
    pure (a', [])
  parseExpr (PPi _ _ _ _ a b) = do
    a' <- parseExpr' a
    b' <- parseExpr' b
    pure (a', b')
  parseExpr b = do
    b' <- parseExpr' b
    pure ([], b')

  isApproximationOf : (given : Name)
                   -> (candidate : Name)
                   -> Bool
  isApproximationOf (NS ns n) (NS ns' n') =
    n == n' && Namespace.isApproximationOf ns ns'
  isApproximationOf (UN n) (NS ns' (UN n')) =
    n == n'
  isApproximationOf (NS ns n) _ =
    False
  isApproximationOf (UN n) (UN n') =
    n == n'
  isApproximationOf _ _ =
    False

  isApproximationOf' : (given : NameOrConst)
                    -> (candidate : NameOrConst)
                    -> Bool
  isApproximationOf' (AName x) (AName y) =
    isApproximationOf x y
  isApproximationOf' a b = eqConst a b

  ||| Find all name and type literal occurrences.
  export
  doFind : List NameOrConst -> Term vars -> List NameOrConst
  doFind ns (Local fc x idx y) = ns
  doFind ns (Ref fc x name) = AName name :: ns
  doFind ns (Meta fc n i xs)
      = foldl doFind ns xs
  doFind ns (Bind fc x (Let _ c val ty) scope)
      = doFind (doFind (doFind ns val) ty) scope
  doFind ns (Bind fc x b scope)
      = doFind (doFind ns (binderType b)) scope
  doFind ns (App fc fn arg)
      = doFind (doFind ns fn) arg
  doFind ns (As fc s as tm) = doFind ns tm
  doFind ns (TDelayed fc x y) = doFind ns y
  doFind ns (TDelay fc x t y)
      = doFind (doFind ns t) y
  doFind ns (TForce fc r x) = doFind ns x
  doFind ns (PrimVal fc c) =
    fromMaybe [] ((:: []) <$> parseNameOrConst (PPrimVal fc c)) ++ ns
  doFind ns (Erased fc i) = ns
  doFind ns (TType fc _) = AType :: ns

  toFullNames' : NameOrConst -> Core NameOrConst
  toFullNames' (AName x) = AName <$> toFullNames x
  toFullNames' x = pure x

  fuzzyMatch : (neg : List NameOrConst)
            -> (pos : List NameOrConst)
            -> Term vars
            -> Core Bool
  fuzzyMatch neg pos (Bind _ _ b sc) = do
    let refsB = doFind [] (binderType b)
    refsB <- traverse toFullNames' refsB
    let neg' = diffBy isApproximationOf' neg refsB
    fuzzyMatch neg' pos sc
  fuzzyMatch (_ :: _) pos tm = pure False
  fuzzyMatch [] pos tm = do
    let refsB = doFind [] tm
    refsB <- traverse toFullNames' refsB
    pure (isNil $ diffBy isApproximationOf' pos refsB)

  predicate :  (neg : List NameOrConst)
            -> (pos : List NameOrConst)
            -> GlobalDef
            -> Core Bool
  predicate neg pos def = case definition def of
    Hole {} => pure False
    _ => fuzzyMatch neg pos def.type
