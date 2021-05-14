module Idris.REPL.FuzzySearch

import Core.AutoSearch
import Core.CaseTree
import Core.CompileExpr
import Core.Context
import Core.Context.Log
import Core.Env
import Core.InitPrimitives
import Core.LinearCheck
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.Termination
import Core.TT
import Core.Unify

import Idris.Desugar
import Idris.DocString
import Idris.Error
import Idris.IDEMode.CaseSplit
import Idris.IDEMode.Commands
import Idris.IDEMode.MakeClause
import Idris.IDEMode.Holes
import Idris.ModTree
import Idris.Parser
import Idris.Pretty
import Idris.ProcessIdr
import Idris.Resugar
import Idris.Syntax
import Idris.Version

import public Idris.REPL.Common

import Data.List
import Data.List1
import Data.Maybe
import Libraries.Data.ANameMap
import Libraries.Data.NameMap
import Libraries.Data.PosMap
import Data.Stream
import Data.Strings
import Data.DPair
import Libraries.Data.String.Extra
import Libraries.Data.List.Extra
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util
import Libraries.Text.PrettyPrint.Prettyprinter.Render.Terminal
import Libraries.Utils.Path
import Libraries.System.Directory.Tree

import System
import System.File
import System.Directory

export
fuzzySearch : {auto c : Ref Ctxt Defs}
           -> {auto u : Ref UST UState}
           -> {auto s : Ref Syn SyntaxInfo}
           -> {auto m : Ref MD Metadata}
           -> {auto o : Ref ROpts REPLOpts}
           -> PTerm
           -> Core REPLResult
fuzzySearch expr = do
  let Just (neg, pos) = parseExpr expr
    | _ => pure (REPLError (pretty "Bad expression, expected"
                       <++> code (pretty "B")
                       <++> pretty "or"
                       <++> code (pretty "_ -> B")
                       <++> pretty "or"
                       <++> code (pretty "A -> B")
                       <+> pretty ", where"
                       <++> code (pretty "A")
                       <++> pretty "and"
                       <++> code (pretty "B")
                       <++> pretty "are spines of global names"))
  defs <- branch
  let curr = currentNS defs
  let ctxt = gamma defs
  filteredDefs <-
    do names   <- allNames ctxt
       defs    <- traverse (flip lookupCtxtExact ctxt) names
       let defs = flip mapMaybe defs $ \ md =>
                      do d <- md
                         guard (visibleIn curr (fullname d) (visibility d))
                         guard (isJust $ userNameRoot (fullname d))
                         pure d
       allDefs <- traverse (resolved ctxt) defs
       filterM (\def => fuzzyMatch neg pos def.type) allDefs
  put Ctxt defs
  doc <- traverse (docsOrSignature replFC) $ fullname <$> filteredDefs
  pure $ Printed $ vsep $ pretty <$> (intersperse "\n" $ join doc)
 where

  data NameOrConst = AName Name
                   | AInt
                   | AInteger
                   | ABits8
                   | ABits16
                   | ABits32
                   | ABits64
                   | AString
                   | AChar
                   | ADouble
                   | AWorld
                   | AType

  eqConst : (x, y : NameOrConst) -> Bool
  eqConst AInt     AInt     = True
  eqConst AInteger AInteger = True
  eqConst ABits8   ABits8   = True
  eqConst ABits16  ABits16  = True
  eqConst ABits32  ABits32  = True
  eqConst ABits64  ABits64  = True
  eqConst AString  AString  = True
  eqConst AChar    AChar    = True
  eqConst ADouble  ADouble  = True
  eqConst AWorld   AWorld   = True
  eqConst AType    AType    = True
  eqConst _        _        = False

  parseNameOrConst : PTerm -> Maybe NameOrConst
  parseNameOrConst (PRef _ n)               = Just (AName n)
  parseNameOrConst (PPrimVal _ IntType)     = Just AInt
  parseNameOrConst (PPrimVal _ IntegerType) = Just AInteger
  parseNameOrConst (PPrimVal _ Bits8Type)   = Just ABits8
  parseNameOrConst (PPrimVal _ Bits16Type)  = Just ABits16
  parseNameOrConst (PPrimVal _ Bits32Type)  = Just ABits32
  parseNameOrConst (PPrimVal _ Bits64Type)  = Just ABits64
  parseNameOrConst (PPrimVal _ StringType)  = Just AString
  parseNameOrConst (PPrimVal _ CharType)    = Just AChar
  parseNameOrConst (PPrimVal _ DoubleType)  = Just ADouble
  parseNameOrConst (PPrimVal _ WorldType)   = Just AWorld
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
  doFind ns (TType fc) = AType :: ns

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
