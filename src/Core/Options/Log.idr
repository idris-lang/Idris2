module Core.Options.Log

import public Data.List
import Data.List1
import public Data.Maybe
import Libraries.Data.StringMap
import Libraries.Data.StringTrie
import Data.Strings
import Data.These
import Libraries.Text.PrettyPrint.Prettyprinter

%default total

||| Log levels are characterised by two things:
||| * a dot-separated path of ever finer topics of interest e.g. scope.let
||| * a natural number corresponding to the verbosity level e.g. 5
|||
||| If the user asks for some logs by writing
|||
|||     %log scope 5
|||
||| they will get all of the logs whose path starts with `scope` and whose
||| verbosity level is less or equal to `5`. By combining different logging
||| directives, users can request information about everything (with a low
||| level of details) and at the same time focus on a particular subsystem
||| they want to get a lot of information about. For instance:
|||
|||     %log 1
|||     %log scope.let 10
|||
||| will deliver basic information about the various phases the compiler goes
||| through and deliver a lot of information about scope-checking let binders.

----------------------------------------------------------------------------------
-- INDIVIDUAL LOG LEVEL

public export
knownTopics : List (String,String)
knownTopics = [
    ("auto", "some documentation of this option"),
    ("builtin.Natural", "some documentation of this option"),
    ("builtin.Natural.addTransform", "some documentation of this option"),
    ("builtin.NaturalToInteger", "some documentation of this option"),
    ("builtin.NaturalToInteger.addTransforms", "some documentation of this option"),
    ("builtin.IntegerToNatural", "some documentation of this option"),
    ("builtin.IntegerToNatural.addTransforms", "some documentation of this option"),
    ("compile.casetree", "some documentation of this option"),
    ("compile.casetree.clauses", "some documentation of this option"),
    ("compile.casetree.getpmdef", "some documentation of this option"),
    ("compile.casetree.intermediate", "some documentation of this option"),
    ("compile.casetree.pick", "some documentation of this option"),
    ("compile.casetree.partition", "some documentation of this option"),
    ("compiler.inline.eval", "some documentation of this option"),
    ("compiler.refc", "some documentation of this option"),
    ("compiler.refc.cc", "some documentation of this option"),
    ("compiler.scheme.chez", "some documentation of this option"),
    ("coverage", "some documentation of this option"),
    ("coverage.empty", "some documentation of this option"),
    ("coverage.missing", "some documentation of this option"),
    ("coverage.recover", "some documentation of this option"),
    ("declare.data", "some documentation of this option"),
    ("declare.data.constructor", "some documentation of this option"),
    ("declare.data.parameters", "some documentation of this option"),
    ("declare.def", "some documentation of this option"),
    ("declare.def.clause", "some documentation of this option"),
    ("declare.def.clause.impossible", "some documentation of this option"),
    ("declare.def.clause.with", "some documentation of this option"),
    ("declare.def.impossible", "some documentation of this option"),
    ("declare.def.lhs", "some documentation of this option"),
    ("declare.def.lhs.implicits", "some documentation of this option"),
    ("declare.param", "some documentation of this option"),
    ("declare.record", "some documentation of this option"),
    ("declare.record.field", "some documentation of this option"),
    ("declare.record.projection", "some documentation of this option"),
    ("declare.record.projection.prefix", "some documentation of this option"),
    ("declare.type", "some documentation of this option"),
    ("desugar.idiom", "some documentation of this option"),
    ("doc.record", "some documentation of this option"),
    ("elab", "some documentation of this option"),
    ("elab.ambiguous", "some documentation of this option"),
    ("elab.app.lhs", "some documentation of this option"),
    ("elab.as", "some documentation of this option"),
    ("elab.bindnames", "some documentation of this option"),
    ("elab.binder", "some documentation of this option"),
    ("elab.case", "some documentation of this option"),
    ("elab.def.local", "some documentation of this option"),
    ("elab.delay", "some documentation of this option"),
    ("elab.hole", "some documentation of this option"),
    ("elab.implicits", "some documentation of this option"),
    ("elab.implementation", "some documentation of this option"),
    ("elab.interface", "some documentation of this option"),
    ("elab.interface.default", "some documentation of this option"),
    ("elab.local", "some documentation of this option"),
    ("elab.prun", "some documentation of this option"),
    ("elab.prune", "some documentation of this option"),
    ("elab.record", "some documentation of this option"),
    ("elab.retry", "some documentation of this option"),
    ("elab.rewrite", "some documentation of this option"),
    ("elab.unify", "some documentation of this option"),
    ("elab.update", "some documentation of this option"),
    ("elab.with", "some documentation of this option"),
    ("eval.casetree", "some documentation of this option"),
    ("eval.casetree.stuck", "some documentation of this option"),
    ("eval.eta", "some documentation of this option"),
    ("eval.stuck", "some documentation of this option"),
    ("idemode.hole", "some documentation of this option"),
    ("ide-mode.highlight", "some documentation of this option"),
    ("ide-mode.highlight.alias", "some documentation of this option"),
    ("ide-mode.send", "some documentation of this option"),
    ("import", "some documentation of this option"),
    ("import.file", "some documentation of this option"),
    ("interaction.casesplit", "some documentation of this option"),
    ("interaction.generate", "some documentation of this option"),
    ("interaction.search", "some documentation of this option"),
    ("metadata.names", "some documentation of this option"),
    ("module.hash", "some documentation of this option"),
    ("quantity", "some documentation of this option"),
    ("quantity.hole", "some documentation of this option"),
    ("quantity.hole.update", "some documentation of this option"),
    ("repl.eval", "some documentation of this option"),
    ("specialise", "some documentation of this option"),
    ("totality", "some documentation of this option"),
    ("totality.positivity", "some documentation of this option"),
    ("totality.termination", "some documentation of this option"),
    ("totality.termination.calc", "some documentation of this option"),
    ("totality.termination.guarded", "some documentation of this option"),
    ("totality.termination.sizechange", "some documentation of this option"),
    ("totality.termination.sizechange.checkCall", "some documentation of this option"),
    ("totality.termination.sizechange.checkCall.inPath", "some documentation of this option"),
    ("totality.termination.sizechange.checkCall.inPathNot.restart", "some documentation of this option"),
    ("totality.termination.sizechange.checkCall.inPathNot.return", "some documentation of this option"),
    ("totality.termination.sizechange.inPath", "some documentation of this option"),
    ("totality.termination.sizechange.isTerminating", "some documentation of this option"),
    ("totality.termination.sizechange.needsChecking", "some documentation of this option"),
    ("transform.lhs", "some documentation of this option"),
    ("transform.rhs", "some documentation of this option"),
    ("ttc.read", "some documentation of this option"),
    ("ttc.write", "some documentation of this option"),
    ("typesearch.equiv", "some documentation of this option"),
    ("unelab.case", "some documentation of this option"),
    ("unify", "some documentation of this option"),
    ("unify.application", "some documentation of this option"),
    ("unify.binder", "some documentation of this option"),
    ("unify.constant", "some documentation of this option"),
    ("unify.constraint", "some documentation of this option"),
    ("unify.delay", "some documentation of this option"),
    ("unify.equal", "some documentation of this option"),
    ("unify.head", "some documentation of this option"),
    ("unify.hole", "some documentation of this option"),
    ("unify.instantiate", "some documentation of this option"),
    ("unify.invertible", "some documentation of this option"),
    ("unify.meta", "some documentation of this option"),
    ("unify.noeta", "some documentation of this option"),
    ("unify.postpone", "some documentation of this option"),
    ("unify.retry", "some documentation of this option"),
    ("unify.search", "some documentation of this option"),
    ("unify.unsolved", "some documentation of this option")
]

public export
KnownTopic : String -> Type
KnownTopic s = IsJust (lookup s knownTopics)

||| An individual log level is a pair of a list of non-empty strings and a number.
||| We keep the representation opaque to force users to call the smart constructor
export
data LogLevel : Type where
  MkLogLevel : List String -> Nat -> LogLevel

||| If we have already processed the input string into (maybe) a non-empty list of
||| non-empty topics we can safely make a `LogLevel`.
export
mkLogLevel' : Maybe (List1 String) -> Nat -> LogLevel
mkLogLevel' ps n = MkLogLevel (maybe [] forget ps) n

||| The smart constructor makes sure that the empty string is mapped to the empty
||| list. This bypasses the fact that the function `split` returns a non-empty
||| list no matter what.
|||
||| However, invoking this function comes without guarantees that
||| the passed string corresponds to a known topic. For this,
||| use `mkLogLevel`.
|||
||| Use this function to create user defined loglevels, for instance, during
||| elaborator reflection.
export
mkUnverifiedLogLevel : (s : String) -> Nat -> LogLevel
mkUnverifiedLogLevel "" = mkLogLevel' Nothing
mkUnverifiedLogLevel ps = mkLogLevel' (Just (split (== '.') ps))

||| Like `mkUnverifiedLogLevel` but with a compile time check that
||| the passed string is a known topic.
export
mkLogLevel : (s : String) -> {auto 0 _ : KnownTopic s} -> Nat -> LogLevel
mkLogLevel s = mkUnverifiedLogLevel s

||| The unsafe constructor should only be used in places where the topic has already
||| been appropriately processed.
export
unsafeMkLogLevel : List String -> Nat -> LogLevel
unsafeMkLogLevel = MkLogLevel

||| The topics attached to a `LogLevel` can be reconstructed from the list of strings.
export
topics : LogLevel -> List String
topics (MkLogLevel ps _) = ps

||| The verbosity is provided by the natural number
export
verbosity : LogLevel -> Nat
verbosity (MkLogLevel _ n) = n

||| When writing generic functions we sometimes want to keep the same topic but
||| change the verbosity.
export
withVerbosity : Nat -> LogLevel -> LogLevel
withVerbosity n (MkLogLevel ps _) = MkLogLevel ps n

||| A log level is show as `P.Q.R:N` where `P`, `Q` and `R` are topics and `N` is
||| a verbosity level. If there are no topics then we simply print `N`.
export
Show LogLevel where

  show (MkLogLevel ps n) = case ps of
    [] => show n
    _  => fastAppend (intersperse "." ps) ++ ":" ++ show n

export
Pretty LogLevel where

  pretty = pretty . show

export
parseLogLevel : String -> Maybe LogLevel
parseLogLevel str = do
  (c, n) <- let nns = split (== ':') str
                n = head nns
                ns = tail nns in
                case ns of
                     [] => pure (MkLogLevel [], n)
                     [ns] => pure (mkUnverifiedLogLevel n, ns)
                     _ => Nothing
  lvl <- parsePositive n
  pure $ c (fromInteger lvl)

----------------------------------------------------------------------------------
-- COLLECTION OF LOG LEVELS

||| We store the requested log levels in a Trie which makes it easy to check
||| whether a given log level is captured by the user's request for information.
export
LogLevels : Type
LogLevels = StringTrie Nat

||| By default we log everything but with very few details (i.e. next to nothing)
export
defaultLogLevel : LogLevels
defaultLogLevel = singleton [] 0

export
insertLogLevel : LogLevel -> LogLevels -> LogLevels
insertLogLevel (MkLogLevel ps n) = insert ps n

----------------------------------------------------------------------------------
-- CHECKING WHETHER TO LOG

||| We keep a log if there is a prefix of its path associated to a larger number
||| in the LogLevels.
export
keepLog : LogLevel -> LogLevels -> Bool
keepLog (MkLogLevel _ Z) _ = True
keepLog (MkLogLevel path n) levels = go path levels where

  go : List String -> StringTrie Nat -> Bool
  go path (MkStringTrie current) = here || there where

    here : Bool
    here = case fromThis current of
      Nothing => False
      Just m  => n <= m

    there : Bool
    there = case path of
      [] => False
      (p :: rest) => fromMaybe False $ do
        assoc <- fromThat current
        next  <- lookup p assoc
        pure $ go rest next
