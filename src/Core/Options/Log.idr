module Core.Options.Log

import Data.List
import Data.List1
import Data.Maybe
import Data.StringMap
import Data.StringTrie
import Data.Strings
import Data.These
import Text.PrettyPrint.Prettyprinter

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
export
mkLogLevel : String -> Nat -> LogLevel
mkLogLevel "" = mkLogLevel' Nothing
mkLogLevel ps = mkLogLevel' (Just (split (== '.') ps))

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
  (c, n) <- case split (== ':') str of
             n ::: [] => pure (MkLogLevel [], n)
             ps ::: [n] => pure (mkLogLevel ps, n)
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
insertLogLevel (MkLogLevel ps n) = insertWith ps (maybe n (max n))

----------------------------------------------------------------------------------
-- CHECKING WHETHER TO LOG

||| We keep a log if there is a prefix of its path associated to a larger number
||| in the LogLevels.
export
keepLog : LogLevel -> LogLevels -> Bool
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
