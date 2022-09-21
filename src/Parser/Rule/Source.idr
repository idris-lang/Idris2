module Parser.Rule.Source

import public Parser.Lexer.Source
import public Parser.Support

import Core.Context
import Core.TT
import Core.Metadata
import Data.List1
import Data.SnocList
import Data.String
import Libraries.Data.List.Extra

%default total

||| This version of the Parser's state is parameterized over
||| the container for SemanticDecorations. The parser should
||| only work the ParsingState type below and after parsing
||| is complete, use the regular State type.
public export
record ParserState (container : Type -> Type) where
  constructor MkState
  decorations : container ASemanticDecoration
  holeNames : List String

||| This state needs to provide efficient concatenation.
public export
ParsingState : Type
ParsingState = ParserState SnocList

||| This is the final state after parsing. We no longer
||| need to support efficient concatenation.
public export
State : Type
State = ParserState List

export
toState : ParsingState -> State
toState (MkState decs hs) = MkState (cast decs) hs

-- To help prevent concatenation slow downs, we only
-- provide Semigroup and Monoid for the efficient
-- version of the ParserState.
export
Semigroup ParsingState where
  MkState decs1 hs1 <+> MkState decs2 hs2
    = MkState (decs1 <+> decs2) (hs1 ++ hs2)

export
Monoid ParsingState where
  neutral = MkState [<] []

public export
BRule : Bool -> Type -> Type
BRule = Grammar ParsingState Token

public export
Rule : Type -> Type
Rule = BRule True

public export
EmptyRule : Type -> Type
EmptyRule = BRule False

export
actD : ASemanticDecoration -> EmptyRule ()
actD s = act (MkState [<s] [])

export
actH : String -> EmptyRule ()
actH s = act (MkState [<] [s])

export
eoi : EmptyRule ()
eoi = ignore $ nextIs "Expected end of input" isEOI
  where
    isEOI : Token -> Bool
    isEOI EndInput = True
    isEOI _ = False

export
constant : Rule Constant
constant
    = terminal "Expected constant" $ \case
        CharLit c    => Ch <$> getCharLit c
        DoubleLit d  => Just (Db d)
        IntegerLit i => Just (BI i)
        Ident s      => isConstantType (UN $ Basic s) >>=
                             \case WorldType => Nothing
                                   c         => Just $ PrT c
        _            => Nothing

documentation' : Rule String
documentation' = terminal "Expected documentation comment" $
                          \case
                            DocComment d => Just d
                            _ => Nothing

export
decorationFromBounded : OriginDesc -> Decoration -> WithBounds a -> ASemanticDecoration
decorationFromBounded fname decor bnds
   = ((fname, start bnds, end bnds), decor, Nothing)

documentation : OriginDesc -> Rule String
documentation fname
  = do b <- bounds (some documentation')
       actD (decorationFromBounded fname Comment b)
       pure (unlines $ forget b.val)

export
optDocumentation : OriginDesc -> EmptyRule String
optDocumentation fname = option "" (documentation fname)

export
intLit : Rule Integer
intLit
    = terminal "Expected integer literal" $
               \case
                 IntegerLit i => Just i
                 _ => Nothing

export
onOffLit : Rule Bool
onOffLit
    = terminal "Expected on or off" $
               \case
                 Ident "on" => Just True
                 Ident "off" => Just False
                 _ => Nothing

export
strLit : Rule String
strLit
    = terminal "Expected string literal" $
               \case
                 StringLit n s => escape n s
                 _ => Nothing

||| String literal split by line wrap (not striped) before escaping the string.
export
strLitLines : Rule (List1 String)
strLitLines
    = terminal "Expected string literal" $
               \case
                 StringLit n s =>
                   traverse (escape n . fastPack)
                            (splitAfter isNL (fastUnpack s))
                 _ => Nothing

export
strBegin : Rule ()
strBegin = terminal "Expected string begin" $
                    \case
                      StringBegin Single => Just ()
                      _ => Nothing

export
multilineBegin : Rule ()
multilineBegin = terminal "Expected multiline string begin" $
                          \case
                            StringBegin Multi => Just ()
                            _ => Nothing

export
strEnd : Rule ()
strEnd = terminal "Expected string end" $
                  \case
                    StringEnd => Just ()
                    _ => Nothing

export
interpBegin : Rule ()
interpBegin = terminal "Expected string interp begin" $
                       \case
                         InterpBegin => Just ()
                         _ => Nothing

export
interpEnd : Rule ()
interpEnd = terminal "Expected string interp end" $
                     \case
                       InterpEnd => Just ()
                       _ => Nothing

export
simpleStr : Rule String
simpleStr = strBegin *> commit *> (option "" strLit) <* strEnd

export
aDotIdent : Rule String
aDotIdent = terminal "Expected dot+identifier" $
                     \case
                       DotIdent s => Just s
                       _ => Nothing

export
postfixProj : Rule Name
postfixProj = UN . Field <$> aDotIdent

export
symbol : String -> Rule ()
symbol req
    = terminal ("Expected '" ++ req ++ "'") $
               \case
                 Symbol s => guard (s == req)
                 _ => Nothing

export
anyReservedSymbol : Rule String
anyReservedSymbol
  = terminal ("Expected a reserved symbol") $
               \case
                 Symbol s => s <$ guard (s `elem` reservedSymbols)
                 _ => Nothing

export
anyKeyword : Rule String
anyKeyword
  = terminal ("Expected a keyword") $
             \case
               Keyword s => Just s
               _ => Nothing

export
keyword : String -> Rule ()
keyword req
    = terminal ("Expected '" ++ req ++ "'") $
               \case
                 Keyword s => guard (s == req)
                 _ => Nothing

export
exactIdent : String -> Rule ()
exactIdent req
    = terminal ("Expected " ++ req) $
               \case
                 Ident s => guard (s == req)
                 _ => Nothing

export
pragma : String -> Rule ()
pragma n =
  terminal ("Expected pragma " ++ n) $
    \case
      Pragma s => guard (s == n)
      _ => Nothing

export
builtinType : Rule BuiltinType
builtinType =
    BuiltinNatural <$ exactIdent "Natural"
    <|> NaturalToInteger <$ exactIdent "NaturalToInteger"
    <|> IntegerToNatural <$ exactIdent "IntegerToNatural"

operatorCandidate : Rule Name
operatorCandidate
    = terminal "Expected operator" $
               \case
                 Symbol s => Just (UN $ Basic s) -- TODO: have an operator construct?
                 _ => Nothing

export
unqualifiedOperatorName : Rule String
unqualifiedOperatorName
    = terminal "Expected operator" $
               \case
                 Symbol s => s <$ guard (not $ s `elem` reservedSymbols)
                 _ => Nothing

export
operator : Rule Name
operator = UN . Basic <$> unqualifiedOperatorName
               -- ^ TODO: add an operator constructor?

identPart : Rule String
identPart
    = terminal "Expected name" $
               \case
                 Ident str => Just str
                 _ => Nothing

export
namespacedIdent : Rule (Maybe Namespace, String)
namespacedIdent
    = terminal "Expected namespaced name" $
               \case
                 DotSepIdent ns n => Just (Just ns, n)
                 Ident i => Just (Nothing, i)
                 _ => Nothing

isCapitalisedIdent : WithBounds String -> EmptyRule ()
isCapitalisedIdent str =
  let val = str.val
      loc = str.bounds
      err : EmptyRule ()
          = failLoc loc ("Expected a capitalised identifier, got: " ++ val)
  in case strM val of
       StrNil => err
       StrCons c _ => if (isUpper c || c > chr 160) then pure () else err


export
namespaceId : Rule Namespace
namespaceId = do
  nsid <- bounds namespacedIdent
  isCapitalisedIdent (snd <$> nsid)
  pure (uncurry mkNestedNamespace nsid.val)

export
namespacedSymbol : String -> Rule (Maybe Namespace)
namespacedSymbol req = do
  (symbol req $> Nothing) <|> do
    ns <- namespaceId
    symbol ("." ++ req)
    pure (Just ns)

export
moduleIdent : Rule ModuleIdent
moduleIdent = nsAsModuleIdent <$> namespaceId

export
unqualifiedName : Rule String
unqualifiedName = identPart

export
holeName : Rule String
holeName
    = terminal "Expected hole name" $
               \case
                 HoleIdent str => Just str
                 _ => Nothing

reservedNames : List String
reservedNames
    = [ "Type", "Int", "Int8", "Int16", "Int32", "Int64", "Integer"
      , "Bits8", "Bits16", "Bits32", "Bits64"
      , "String", "Char", "Double", "Lazy", "Inf", "Force", "Delay"
      ]

isNotReservedName : WithBounds String -> EmptyRule ()
isNotReservedName x
    = when (x.val `elem` reservedNames) $
        failLoc x.bounds $ "Can't use reserved name \{x.val}"

isNotReservedSymbol : WithBounds String -> EmptyRule ()
isNotReservedSymbol x
    = when (x.val `elem` reservedSymbols) $
        failLoc x.bounds $ "Can't use reserved symbol \{x.val}"

export
opNonNS : Rule Name
opNonNS = do
  symbol "("
  commit
  id <- bounds (operatorCandidate <|> postfixProj)
  isNotReservedSymbol (nameRoot <$> id)
  symbol ")"
  pure id.val

identWithCapital : (capitalised : Bool) -> WithBounds String ->
                   EmptyRule ()
identWithCapital b x = when b (isCapitalisedIdent x)

nameWithCapital : (capitalised : Bool) -> Rule Name
nameWithCapital b = opNonNS <|> do
  nsx <- bounds namespacedIdent
  opNS nsx <|> nameNS nsx
 where

  nameNS : WithBounds (Maybe Namespace, String) -> EmptyRule Name
  nameNS nsx = do
    let id = snd <$> nsx
    identWithCapital b id
    isNotReservedName id
    pure $ uncurry mkNamespacedName (map Basic nsx.val)

  opNS : WithBounds (Maybe Namespace, String) -> Rule Name
  opNS nsx = do
    isCapitalisedIdent (snd <$> nsx)
    let ns = uncurry mkNestedNamespace nsx.val
    symbol ".("
    n <- (operator <|> postfixProj)
    symbol ")"
    pure (NS ns n)

export
name : Rule Name
name = nameWithCapital False

export
capitalisedName : Rule Name
capitalisedName = nameWithCapital True

export
capitalisedIdent : Rule String
capitalisedIdent = do
  id <- bounds identPart
  isCapitalisedIdent id
  isNotReservedName id
  pure id.val

export
dataConstructorName : Rule Name
dataConstructorName = opNonNS <|> (UN . Basic) <$> capitalisedIdent

export %inline
dataTypeName : Rule Name
dataTypeName = opNonNS <|> capitalisedName

export
IndentInfo : Type
IndentInfo = Int

export
init : IndentInfo
init = 0

continueF : EmptyRule () -> (indent : IndentInfo) -> EmptyRule ()
continueF err indent
    = do eoi; err
  <|> do keyword "where"; err
  <|> do col <- column
         when (col <= indent)
            err

||| Fail if this is the end of a block entry or end of file
export
continue : (indent : IndentInfo) -> EmptyRule ()
continue = continueF (fail "Unexpected end of expression")

||| As 'continue' but failing is fatal (i.e. entire parse fails)
export
mustContinue : (indent : IndentInfo) -> Maybe String -> EmptyRule ()
mustContinue indent Nothing
   = continueF (fatalError "Unexpected end of expression") indent
mustContinue indent (Just req)
   = continueF (fatalError ("Expected '" ++ req ++ "'")) indent

data ValidIndent =
  |||  In {}, entries can begin in any column
  AnyIndent |
  ||| Entry must begin in a specific column
  AtPos Int |
  ||| Entry can begin in this column or later
  AfterPos Int |
  ||| Block is finished
  EndOfBlock

Show ValidIndent where
  show AnyIndent = "[any]"
  show (AtPos i) = "[col " ++ show i ++ "]"
  show (AfterPos i) = "[after " ++ show i ++ "]"
  show EndOfBlock = "[EOB]"

checkValid : ValidIndent -> Int -> EmptyRule ()
checkValid AnyIndent c = pure ()
checkValid (AtPos x) c = unless (c == x) $ fail "Invalid indentation"
checkValid (AfterPos x) c = unless (c >= x) $ fail "Invalid indentation"
checkValid EndOfBlock c = fail "End of block"

||| Any token which indicates the end of a statement/block/expression
isTerminator : Token -> Bool
isTerminator (Symbol ",") = True
isTerminator (Symbol "]") = True
isTerminator (Symbol ";") = True
isTerminator (Symbol "}") = True
isTerminator (Symbol ")") = True
isTerminator (Symbol "|") = True
isTerminator (Symbol "**") = True
isTerminator (Keyword "in") = True
isTerminator (Keyword "then") = True
isTerminator (Keyword "else") = True
isTerminator (Keyword "where") = True
isTerminator InterpEnd = True
isTerminator EndInput = True
isTerminator _ = False

||| Check we're at the end of a block entry, given the start column
||| of the block.
||| It's the end if we have a terminating token, or the next token starts
||| in or before indent. Works by looking ahead but not consuming.
export
atEnd : (indent : IndentInfo) -> EmptyRule ()
atEnd indent
    = eoi
  <|> do ignore $ nextIs "Expected end of block" isTerminator
  <|> do col <- column
         when (not (col <= indent))
            $ fail "Not the end of a block entry"

-- Check we're at the end, but only by looking at indentation
export
atEndIndent : (indent : IndentInfo) -> EmptyRule ()
atEndIndent indent
    = eoi
  <|> do col <- column
         when (not (col <= indent))
            $ fail "Not the end of a block entry"


-- Parse a terminator, return where the next block entry
-- must start, given where the current block entry started
terminator : ValidIndent -> Int -> EmptyRule ValidIndent
terminator valid laststart
    = do eoi
         pure EndOfBlock
  <|> do symbol ";"
         pure (afterSemi valid)
  <|> do col <- column
         afterDedent valid col
  <|> pure EndOfBlock
 where
   -- Expected indentation for the next token can either be anything (if
   -- we're inside a brace delimited block) or anywhere after the initial
   -- column (if we're inside an indentation delimited block)
   afterSemi : ValidIndent -> ValidIndent
   afterSemi AnyIndent = AnyIndent -- in braces, anything goes
   afterSemi (AtPos c) = AfterPos c -- not in braces, after the last start position
   afterSemi (AfterPos c) = AfterPos c
   afterSemi EndOfBlock = EndOfBlock

   -- Expected indentation for the next token can either be anything (if
   -- we're inside a brace delimited block) or in exactly the initial column
   -- (if we're inside an indentation delimited block)
   afterDedent : ValidIndent -> Int -> EmptyRule ValidIndent
   afterDedent AnyIndent col
       = if col <= laststart
            then pure AnyIndent
            else fail "Not the end of a block entry"
   afterDedent (AfterPos c) col
       = if col <= laststart
            then pure (AtPos c)
            else fail "Not the end of a block entry"
   afterDedent (AtPos c) col
       = if col <= laststart
            then pure (AtPos c)
            else fail "Not the end of a block entry"
   afterDedent EndOfBlock col = pure EndOfBlock

-- Parse an entry in a block
blockEntry : ValidIndent -> (IndentInfo -> Rule ty) ->
             Rule (ty, ValidIndent)
blockEntry valid rule
    = do col <- column
         checkValid valid col
         p <- rule col
         valid' <- terminator valid col
         pure (p, valid')

blockEntries : ValidIndent -> (IndentInfo -> Rule ty) ->
               EmptyRule (List ty)
blockEntries valid rule
     = do eoi; pure []
   <|> do res <- blockEntry valid rule
          ts <- blockEntries (snd res) rule
          pure (fst res :: ts)
   <|> pure []

export
block : (IndentInfo -> Rule ty) -> EmptyRule (List ty)
block item
    = do symbol "{"
         commit
         ps <- blockEntries AnyIndent item
         symbol "}"
         pure ps
  <|> do col <- column
         blockEntries (AtPos col) item


||| `blockAfter col rule` parses a `rule`-block indented by at
||| least `col` spaces (unless the block is explicitly delimited
||| by curly braces). `rule` is a function of the actual indentation
||| level.
export
blockAfter : Int -> (IndentInfo -> Rule ty) -> EmptyRule (List ty)
blockAfter mincol item
    = do symbol "{"
         commit
         ps <- blockEntries AnyIndent item
         symbol "}"
         pure ps
  <|> do col <- column
         ifThenElse (col <= mincol)
            (pure [])
            $ blockEntries (AtPos col) item

export
blockWithOptHeaderAfter :
   (column : Int) ->
   (header : IndentInfo -> Rule hd) ->
   (item : IndentInfo -> Rule ty) ->
   EmptyRule (Maybe hd, List ty)
blockWithOptHeaderAfter {ty} mincol header item
    = do symbol "{"
         commit
         hidt <- optional $ blockEntry AnyIndent header
         restOfBlock hidt
  <|> do col <- column
         ifThenElse (col <= mincol)
            (pure (Nothing, []))
            $ do hidt <- optional $ blockEntry (AtPos col) header
                 ps <- blockEntries (AtPos col) item
                 pure (map fst hidt, ps)
  where
  restOfBlock : Maybe (hd, ValidIndent) -> Rule (Maybe hd, List ty)
  restOfBlock (Just (h, idt)) = do ps <- blockEntries idt item
                                   symbol "}"
                                   pure (Just h, ps)
  restOfBlock Nothing = do ps <- blockEntries AnyIndent item
                           symbol "}"
                           pure (Nothing, ps)

export
nonEmptyBlock : (IndentInfo -> Rule ty) -> Rule (List1 ty)
nonEmptyBlock item
    = do symbol "{"
         commit
         res <- blockEntry AnyIndent item
         ps <- blockEntries (snd res) item
         symbol "}"
         pure (fst res ::: ps)
  <|> do col <- column
         res <- blockEntry (AtPos col) item
         ps <- blockEntries (snd res) item
         pure (fst res ::: ps)

||| `nonEmptyBlockAfter col rule` parses a non-empty `rule`-block indented
||| by at least `col` spaces (unless the block is explicitly delimited
||| by curly braces). `rule` is a function of the actual indentation
||| level.
export
nonEmptyBlockAfter : Int -> (IndentInfo -> Rule ty) -> Rule (List1 ty)
nonEmptyBlockAfter mincol item
    = do symbol "{"
         commit
         res <- blockEntry AnyIndent item
         ps <- blockEntries (snd res) item
         symbol "}"
         pure (fst res ::: ps)
  <|> do col <- column
         let False = col <= mincol
            | True => fatalError "Expected an indented non-empty block"
         res <- blockEntry (AtPos col) item
         ps <- blockEntries (snd res) item
         pure (fst res ::: ps)
