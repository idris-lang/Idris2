module Idris.Parser.Basic

import Core.Options
import Core.Metadata
import Idris.Syntax
import Idris.Syntax.Traversals
import public Idris.Parser.Core.Source
import TTImp.TTImp

import public Libraries.Text.Parser
import Data.Either
import Libraries.Data.IMaybe
import Data.List
import Data.List.Quantifiers
import Data.List1
import Data.Maybe
import Data.So
import Data.Nat
import Data.SnocList
import Data.String
import Libraries.Utils.String
import Libraries.Data.WithDefault

import Idris.Parser.Let

%default covering

export
fcBounds : OriginDesc => Rule a -> Rule (WithFC a)
fcBounds a = (.withFC) <$> bounds a

export
addFCBounds : OriginDesc => Rule (WithData ls a) -> Rule (WithData (FC' :: ls) a)
addFCBounds a = (.addFC) <$> bounds a

export
decorate : {a : Type} -> OriginDesc -> Decoration -> Rule a -> Rule a
decorate fname decor rule = do
  res <- bounds rule
  actD (decorationFromBounded fname decor res)
  pure res.val

export
dependentDecorate : {a : Type} -> OriginDesc -> Rule a -> (a -> Decoration) -> Rule a
dependentDecorate fname rule decor = do
  res <- bounds rule
  actD (decorationFromBounded fname (decor res.val) res)
  pure res.val

export
decoratedKeyword : OriginDesc -> String -> Rule ()
decoratedKeyword fname kwd = decorate fname Keyword (keyword kwd)

export
decorateKeywords : {a : Type} -> OriginDesc -> List (WithBounds a) -> EmptyRule ()
decorateKeywords fname xs
  = act $ MkState (cast (map (decorationFromBounded fname Keyword) xs)) []

export
decoratedPragma : OriginDesc -> String -> Rule ()
decoratedPragma fname prg = decorate fname Keyword (pragma prg)

export
decoratedSymbol : OriginDesc -> String -> Rule ()
decoratedSymbol fname smb = decorate fname Keyword (symbol smb)

export
decoratedNamespacedSymbol : OriginDesc -> String -> Rule (Maybe Namespace)
decoratedNamespacedSymbol fname smb =
  decorate fname Keyword $ namespacedSymbol smb

export
parens : {b : _} -> OriginDesc -> BRule b a -> Rule a
parens fname p
  = pure id <* decoratedSymbol fname "("
            <*> p
            <* decoratedSymbol fname ")"

export
curly : {b : _} -> OriginDesc -> BRule b a -> Rule a
curly fname p
  = pure id <* decoratedSymbol fname "{"
            <*> p
            <* decoratedSymbol fname "}"

export
decoratedDataTypeName : OriginDesc -> Rule Name
decoratedDataTypeName fname = decorate fname Typ dataTypeName

export
decoratedDataConstructorName : OriginDesc -> Rule Name
decoratedDataConstructorName fname = decorate fname Data dataConstructorName

export
decoratedSimpleBinderUName : OriginDesc -> Rule Name
decoratedSimpleBinderUName fname = decorate fname Bound userName

export
decoratedSimpleNamedArg : OriginDesc -> Rule String
decoratedSimpleNamedArg fname
  = decorate fname Bound unqualifiedName
  <|> parens fname (decorate fname Bound unqualifiedOperatorName)

-- Some context for the parser
public export
record ParseOpts where
  constructor MkParseOpts
  eqOK : Bool -- = operator is parseable
  withOK : Bool -- = with applications are parseable

export
peq : ParseOpts -> ParseOpts
peq = { eqOK := True }

export
pnoeq : ParseOpts -> ParseOpts
pnoeq = { eqOK := False }

export
pdef : ParseOpts
pdef = MkParseOpts {eqOK = True, withOK = True}

export
pnowith : ParseOpts
pnowith = MkParseOpts {eqOK = True, withOK = False}

export
plhs : ParseOpts
plhs = MkParseOpts {eqOK = False, withOK = False}
