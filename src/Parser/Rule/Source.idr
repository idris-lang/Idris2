module Parser.Rule.Source

import public Parser.Lexer.Source
import public Parser.Rule.Common
import public Parser.Support

import Core.TT

%default total

public export
SourceRule : Type -> Type
SourceRule = Rule SourceToken

public export
SourceEmptyRule : Type -> Type
SourceEmptyRule = EmptyRule SourceToken

export
eoi : SourceEmptyRule ()
eoi
    = do nextIs "Expected end of input" (isEOI . tok)
         pure ()
  where
    isEOI : SourceToken -> Bool
    isEOI EndInput = True
    isEOI _ = False

export
constant : SourceRule Constant
constant
    = terminal "Expected constant"
               (\x => case tok x of
                           Literal i => Just (BI i)
                           StrLit s => case escape s of
                                            Nothing => Nothing
                                            Just s' => Just (Str s')
                           CharLit c => case getCharLit c of
                                             Nothing => Nothing
                                             Just c' => Just (Ch c')
                           DoubleLit d => Just (Db d)
                           NSIdent ["Int"] => Just IntType
                           NSIdent ["Integer"] => Just IntegerType
                           NSIdent ["String"] => Just StringType
                           NSIdent ["Char"] => Just CharType
                           NSIdent ["Double"] => Just DoubleType
                           _ => Nothing)

export
intLit : SourceRule Integer
intLit
    = terminal "Expected integer literal"
               (\x => case tok x of
                           Literal i => Just i
                           _ => Nothing)

export
strLit : SourceRule String
strLit
    = terminal "Expected string literal"
               (\x => case tok x of
                           StrLit s => Just s
                           _ => Nothing)

export
recField : SourceRule Name
recField
    = terminal "Expected record field"
               (\x => case tok x of
                           RecordField s => Just (RF s)
                           _ => Nothing)

export
symbol : String -> SourceRule ()
symbol req
    = terminal ("Expected '" ++ req ++ "'")
               (\x => case tok x of
                           Symbol s => if s == req then Just ()
                                                   else Nothing
                           _ => Nothing)

export
keyword : String -> SourceRule ()
keyword req
    = terminal ("Expected '" ++ req ++ "'")
               (\x => case tok x of
                           Keyword s => if s == req then Just ()
                                                    else Nothing
                           _ => Nothing)

export
exactIdent : String -> SourceRule ()
exactIdent req
    = terminal ("Expected " ++ req)
               (\x => case tok x of
                           NSIdent [s] => if s == req then Just ()
                                                      else Nothing
                           _ => Nothing)

export
pragma : String -> SourceRule ()
pragma n =
  terminal ("Expected pragma " ++ n)
    (\x => case tok x of
      Pragma s =>
        if s == n
          then Just ()
          else Nothing
      _ => Nothing)

export
operator : SourceRule Name
operator
    = terminal "Expected operator"
               (\x => case tok x of
                           Symbol s =>
                                if s `elem` reservedSymbols
                                   then Nothing
                                   else Just (UN s)
                           _ => Nothing)

identPart : SourceRule String
identPart
    = terminal "Expected name"
               (\x => case tok x of
                           NSIdent [str] => Just str
                           _ => Nothing)

export
nsIdent : SourceRule (List String)
nsIdent
    = terminal "Expected namespaced name"
        (\x => case tok x of
            NSIdent ns => Just ns
            _ => Nothing)

export
unqualifiedName : SourceRule String
unqualifiedName = identPart

export
holeName : SourceRule String
holeName
    = terminal "Expected hole name"
               (\x => case tok x of
                           HoleIdent str => Just str
                           _ => Nothing)

reservedNames : List String
reservedNames
    = ["Type", "Int", "Integer", "String", "Char", "Double",
       "Lazy", "Inf", "Force", "Delay"]

export
name : SourceRule Name
name = opNonNS <|> do
  ns <- nsIdent
  opNS ns <|> nameNS ns
 where
  reserved : String -> Bool
  reserved n = n `elem` reservedNames

  nameNS : List String -> Grammar (TokenData SourceToken) False Name
  nameNS [] = pure $ UN "IMPOSSIBLE"
  nameNS [x] = 
    if reserved x
      then fail $ "can't use reserved name " ++ x
      else pure $ UN x
  nameNS (x :: xs) =
    if reserved x
      then fail $ "can't use reserved name " ++ x
      else pure $ NS xs (UN x)

  opNonNS : SourceRule Name
  opNonNS = symbol "(" *> (operator <|> recField) <* symbol ")"

  opNS : List String -> SourceRule Name
  opNS ns = do
    symbol ".("
    n <- (operator <|> recField)
    symbol ")"
    pure (NS ns n)

export
IndentInfo : Type
IndentInfo = Int

export
init : IndentInfo
init = 0

continueF : SourceEmptyRule () -> (indent : IndentInfo) -> SourceEmptyRule ()
continueF err indent
    = do eoi; err
  <|> do keyword "where"; err
  <|> do col <- Common.column
         if col <= indent
            then err
            else pure ()

||| Fail if this is the end of a block entry or end of file
export
continue : (indent : IndentInfo) -> SourceEmptyRule ()
continue = continueF (fail "Unexpected end of expression")

||| As 'continue' but failing is fatal (i.e. entire parse fails)
export
mustContinue : (indent : IndentInfo) -> Maybe String -> SourceEmptyRule ()
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

checkValid : ValidIndent -> Int -> SourceEmptyRule ()
checkValid AnyIndent c = pure ()
checkValid (AtPos x) c = if c == x
                            then pure ()
                            else fail "Invalid indentation"
checkValid (AfterPos x) c = if c >= x
                               then pure ()
                               else fail "Invalid indentation"
checkValid EndOfBlock c = fail "End of block"

||| Any token which indicates the end of a statement/block
isTerminator : SourceToken -> Bool
isTerminator (Symbol ",") = True
isTerminator (Symbol "]") = True
isTerminator (Symbol ";") = True
isTerminator (Symbol "}") = True
isTerminator (Symbol ")") = True
isTerminator (Symbol "|") = True
isTerminator (Keyword "in") = True
isTerminator (Keyword "then") = True
isTerminator (Keyword "else") = True
isTerminator (Keyword "where") = True
isTerminator EndInput = True
isTerminator _ = False

||| Check we're at the end of a block entry, given the start column
||| of the block.
||| It's the end if we have a terminating token, or the next token starts
||| in or before indent. Works by looking ahead but not consuming.
export
atEnd : (indent : IndentInfo) -> SourceEmptyRule ()
atEnd indent
    = eoi
  <|> do nextIs "Expected end of block" (isTerminator . tok)
         pure ()
  <|> do col <- Common.column
         if (col <= indent)
            then pure ()
            else fail "Not the end of a block entry"

-- Check we're at the end, but only by looking at indentation
export
atEndIndent : (indent : IndentInfo) -> SourceEmptyRule ()
atEndIndent indent
    = eoi
  <|> do col <- Common.column
         if col <= indent
            then pure ()
            else fail "Not the end of a block entry"


-- Parse a terminator, return where the next block entry
-- must start, given where the current block entry started
terminator : ValidIndent -> Int -> SourceEmptyRule ValidIndent
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
   afterDedent : ValidIndent -> Int -> SourceEmptyRule ValidIndent
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
blockEntry : ValidIndent -> (IndentInfo -> SourceRule ty) ->
             SourceRule (ty, ValidIndent)
blockEntry valid rule
    = do col <- column
         checkValid valid col
         p <- rule col
         valid' <- terminator valid col
         pure (p, valid')

blockEntries : ValidIndent -> (IndentInfo -> SourceRule ty) ->
               SourceEmptyRule (List ty)
blockEntries valid rule
     = do eoi; pure []
   <|> do res <- blockEntry valid rule
          ts <- blockEntries (snd res) rule
          pure (fst res :: ts)
   <|> pure []

export
block : (IndentInfo -> SourceRule ty) -> SourceEmptyRule (List ty)
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
blockAfter : Int -> (IndentInfo -> SourceRule ty) -> SourceEmptyRule (List ty)
blockAfter mincol item
    = do symbol "{"
         commit
         ps <- blockEntries AnyIndent item
         symbol "}"
         pure ps
  <|> do col <- Common.column
         if col <= mincol
            then pure []
            else blockEntries (AtPos col) item

export
blockWithOptHeaderAfter : Int -> (IndentInfo -> SourceRule hd) -> (IndentInfo -> SourceRule ty) -> SourceEmptyRule (Maybe hd, List ty)
blockWithOptHeaderAfter {ty} mincol header item
    = do symbol "{"
         commit
         hidt <- optional $ blockEntry AnyIndent header
         restOfBlock hidt
  <|> do col <- Common.column
         if col <= mincol
            then pure (Nothing, [])
            else do hidt <- optional $ blockEntry (AtPos col) header
                    ps <- blockEntries (AtPos col) item
                    pure (map fst hidt, ps)
  where
  restOfBlock : Maybe (hd, ValidIndent) -> SourceRule (Maybe hd, List ty)
  restOfBlock (Just (h, idt)) = do ps <- blockEntries idt item
                                   symbol "}"
                                   pure (Just h, ps)
  restOfBlock Nothing = do ps <- blockEntries AnyIndent item
                           symbol "}"
                           pure (Nothing, ps)

export
nonEmptyBlock : (IndentInfo -> SourceRule ty) -> SourceRule (List ty)
nonEmptyBlock item
    = do symbol "{"
         commit
         res <- blockEntry AnyIndent item
         ps <- blockEntries (snd res) item
         symbol "}"
         pure (fst res :: ps)
  <|> do col <- column
         res <- blockEntry (AtPos col) item
         ps <- blockEntries (snd res) item
         pure (fst res :: ps)
