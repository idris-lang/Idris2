module Parser.Support

import public Text.Lexer
import public Parser.Lexer
import public Parser.Unlit
import public Text.Parser

import Core.TT
import Data.List
import Data.List.Views
import System.File

%default total

public export
Rule : Type -> Type
Rule ty = Grammar (TokenData Token) True ty

public export
EmptyRule : Type -> Type
EmptyRule ty = Grammar (TokenData Token) False ty

public export
data ParseError = ParseFail String (Maybe (Int, Int)) (List Token)
                | LexFail (Int, Int, String)
                | FileFail FileError
                | LitFail LiterateError

export
Show ParseError where
  show (ParseFail err loc toks)
      = "Parse error: " ++ err ++ " (next tokens: "
            ++ show (take 10 toks) ++ ")"
  show (LexFail (c, l, str))
      = "Lex error at " ++ show (c, l) ++ " input: " ++ str
  show (FileFail err)
      = "File error: " ++ show err
  show (LitFail (MkLitErr l c str))
      = "Lit error(s) at " ++ show (c, l) ++ " input: " ++ str

export
eoi : EmptyRule ()
eoi
    = do nextIs "Expected end of input" (isEOI . tok)
         pure ()
  where
    isEOI : Token -> Bool
    isEOI EndInput = True
    isEOI _ = False

export
runParserTo : {e : _} ->
              Maybe LiterateStyle -> (TokenData Token -> Bool) ->
              String -> Grammar (TokenData Token) e ty -> Either ParseError ty
runParserTo lit pred str p
    = case unlit lit str of
           Left l => Left $ LitFail l
           Right str =>
             case lexTo pred str of
               Left err => Left $ LexFail err
               Right toks =>
                  case parse p toks of
                       Left (Error err []) =>
                              Left $ ParseFail err Nothing []
                       Left (Error err (t :: ts)) =>
                              Left $ ParseFail err (Just (line t, col t))
                                                   (map tok (t :: ts))
                       Right (val, _) => Right val

export
runParser : {e : _} ->
            Maybe LiterateStyle -> String -> Grammar (TokenData Token) e ty -> Either ParseError ty
runParser lit = runParserTo lit (const False)

export
parseFile : (fn : String) -> Rule ty -> IO (Either ParseError ty)
parseFile fn p
    = do Right str <- readFile fn
             | Left err => pure (Left (FileFail err))
         pure (runParser (isLitFile fn) str p)


-- Some basic parsers used by all the intermediate forms

export
location : EmptyRule (Int, Int)
location
    = do tok <- peek
         pure (line tok, col tok)

export
column : EmptyRule Int
column
    = do (line, col) <- location
         pure col

hex : Char -> Maybe Int
hex '0' = Just 0
hex '1' = Just 1
hex '2' = Just 2
hex '3' = Just 3
hex '4' = Just 4
hex '5' = Just 5
hex '6' = Just 6
hex '7' = Just 7
hex '8' = Just 8
hex '9' = Just 9
hex 'a' = Just 10
hex 'b' = Just 11
hex 'c' = Just 12
hex 'd' = Just 13
hex 'e' = Just 14
hex 'f' = Just 15
hex _ = Nothing

dec : Char -> Maybe Int
dec '0' = Just 0
dec '1' = Just 1
dec '2' = Just 2
dec '3' = Just 3
dec '4' = Just 4
dec '5' = Just 5
dec '6' = Just 6
dec '7' = Just 7
dec '8' = Just 8
dec '9' = Just 9
dec _ = Nothing

oct : Char -> Maybe Int
oct '0' = Just 0
oct '1' = Just 1
oct '2' = Just 2
oct '3' = Just 3
oct '4' = Just 4
oct '5' = Just 5
oct '6' = Just 6
oct '7' = Just 7
oct _ = Nothing

getEsc : String -> Maybe Char
getEsc "NUL" = Just '\NUL'
getEsc "SOH" = Just '\SOH'
getEsc "STX" = Just '\STX'
getEsc "ETX" = Just '\ETX'
getEsc "EOT" = Just '\EOT'
getEsc "ENQ" = Just '\ENQ'
getEsc "ACK" = Just '\ACK'
getEsc "BEL" = Just '\BEL'
getEsc "BS" = Just '\BS'
getEsc "HT" = Just '\HT'
getEsc "LF" = Just '\LF'
getEsc "VT" = Just '\VT'
getEsc "FF" = Just '\FF'
getEsc "CR" = Just '\CR'
getEsc "SO" = Just '\SO'
getEsc "SI" = Just '\SI'
getEsc "DLE" = Just '\DLE'
getEsc "DC1" = Just '\DC1'
getEsc "DC2" = Just '\DC2'
getEsc "DC3" = Just '\DC3'
getEsc "DC4" = Just '\DC4'
getEsc "NAK" = Just '\NAK'
getEsc "SYN" = Just '\SYN'
getEsc "ETB" = Just '\ETB'
getEsc "CAN" = Just '\CAN'
getEsc "EM" = Just '\EM'
getEsc "SUB" = Just '\SUB'
getEsc "ESC" = Just '\ESC'
getEsc "FS" = Just '\FS'
getEsc "GS" = Just '\GS'
getEsc "RS" = Just '\RS'
getEsc "US" = Just '\US'
getEsc "SP" = Just '\SP'
getEsc "DEL" = Just '\DEL'
getEsc str = Nothing

escape' : List Char -> Maybe (List Char)
escape' [] = pure []
escape' ('\\' :: '\\' :: xs) = pure $ '\\' :: !(escape' xs)
escape' ('\\' :: '&' :: xs) = pure !(escape' xs)
escape' ('\\' :: 'a' :: xs) = pure $ '\a' :: !(escape' xs)
escape' ('\\' :: 'b' :: xs) = pure $ '\b' :: !(escape' xs)
escape' ('\\' :: 'f' :: xs) = pure $ '\f' :: !(escape' xs)
escape' ('\\' :: 'n' :: xs) = pure $ '\n' :: !(escape' xs)
escape' ('\\' :: 'r' :: xs) = pure $ '\r' :: !(escape' xs)
escape' ('\\' :: 't' :: xs) = pure $ '\t' :: !(escape' xs)
escape' ('\\' :: 'v' :: xs) = pure $ '\v' :: !(escape' xs)
escape' ('\\' :: '\'' :: xs) = pure $ '\'' :: !(escape' xs)
escape' ('\\' :: '\"' :: xs) = pure $ '\"' :: !(escape' xs)
escape' ('\\' :: 'x' :: xs)
    = case span isHexDigit xs of
           ([], rest) => assert_total (escape' rest)
           (ds, rest) => pure $ cast !(toHex 1 (reverse ds)) ::
                                 !(assert_total (escape' rest))
  where
    toHex : Int -> List Char -> Maybe Int
    toHex _ [] = Just 0
    toHex m (d :: ds)
        = pure $ !(hex (toLower d)) * m + !(toHex (m*16) ds)
escape' ('\\' :: 'o' :: xs)
    = case span isOctDigit xs of
           ([], rest) => assert_total (escape' rest)
           (ds, rest) => pure $ cast !(toOct 1 (reverse ds)) ::
                                 !(assert_total (escape' rest))
  where
    toOct : Int -> List Char -> Maybe Int
    toOct _ [] = Just 0
    toOct m (d :: ds)
        = pure $ !(oct (toLower d)) * m + !(toOct (m*8) ds)
escape' ('\\' :: xs)
    = case span isDigit xs of
           ([], (a :: b :: c :: rest)) =>
               case getEsc (pack (the (List _) [a, b, c])) of
                   Just v => Just (v :: !(assert_total (escape' rest)))
                   Nothing => case getEsc (pack (the (List _) [a, b])) of
                                   Just v => Just (v :: !(assert_total (escape' (c :: rest))))
                                   Nothing => escape' xs
           ([], (a :: b :: [])) =>
               case getEsc (pack (the (List _) [a, b])) of
                   Just v => Just (v :: [])
                   Nothing => escape' xs
           ([], rest) => assert_total (escape' rest)
           (ds, rest) => Just $ cast (cast {to=Int} (pack ds)) ::
                                 !(assert_total (escape' rest))
escape' (x :: xs) = Just $ x :: !(escape' xs)

escape : String -> Maybe String
escape x = pure $ pack !(escape' (unpack x))

getCharLit : String -> Maybe Char
getCharLit str
   = do e <- escape str
        if length e == 1
           then Just (assert_total (prim__strHead e))
           else if length e == 0 -- parsed the NULL character that terminated the string!
                   then Just '\0000'
                   else Nothing

export
constant : Rule Constant
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
intLit : Rule Integer
intLit
    = terminal "Expected integer literal"
               (\x => case tok x of
                           Literal i => Just i
                           _ => Nothing)

export
strLit : Rule String
strLit
    = terminal "Expected string literal"
               (\x => case tok x of
                           StrLit s => Just s
                           _ => Nothing)

export
recField : Rule Name
recField
    = terminal "Expected record field"
               (\x => case tok x of
                           RecordField s => Just (RF s)
                           _ => Nothing)

export
symbol : String -> Rule ()
symbol req
    = terminal ("Expected '" ++ req ++ "'")
               (\x => case tok x of
                           Symbol s => if s == req then Just ()
                                                   else Nothing
                           _ => Nothing)

export
keyword : String -> Rule ()
keyword req
    = terminal ("Expected '" ++ req ++ "'")
               (\x => case tok x of
                           Keyword s => if s == req then Just ()
                                                    else Nothing
                           _ => Nothing)

export
exactIdent : String -> Rule ()
exactIdent req
    = terminal ("Expected " ++ req)
               (\x => case tok x of
                           NSIdent [s] => if s == req then Just ()
                                                      else Nothing
                           _ => Nothing)

export
pragma : String -> Rule ()
pragma n =
  terminal ("Expected pragma " ++ n)
    (\x => case tok x of
      Pragma s =>
        if s == n
          then Just ()
          else Nothing
      _ => Nothing)

export
operator : Rule Name
operator
    = terminal "Expected operator"
               (\x => case tok x of
                           Symbol s =>
                                if s `elem` reservedSymbols
                                   then Nothing
                                   else Just (UN s)
                           _ => Nothing)

identPart : Rule String
identPart
    = terminal "Expected name"
               (\x => case tok x of
                           NSIdent [str] => Just str
                           _ => Nothing)

%hide Prelude.(>>=)

export
nsIdent : Rule (List String)
nsIdent
    = terminal "Expected namespaced name"
        (\x => case tok x of
            NSIdent ns => Just ns
            _ => Nothing)

export
unqualifiedName : Rule String
unqualifiedName = identPart

export
holeName : Rule String
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
name : Rule Name
name = opNonNS <|> do
  ns <- nsIdent
  opNS ns <|> nameNS ns
 where
  reserved : String -> Bool
  reserved n = n `elem` reservedNames

  nameNS : List String -> Grammar (TokenData Token) False Name
  nameNS [] = pure $ UN "IMPOSSIBLE"
  nameNS [x] = 
    if reserved x
      then fail $ "can't use reserved name " ++ x
      else pure $ UN x
  nameNS (x :: xs) =
    if reserved x
      then fail $ "can't use reserved name " ++ x
      else pure $ NS xs (UN x)

  opNonNS : Rule Name
  opNonNS = symbol "(" *> (operator <|> recField) <* symbol ")"

  opNS : List String -> Rule Name
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

%hide Prelude.pure

continueF : EmptyRule () -> (indent : IndentInfo) -> EmptyRule ()
continueF err indent
    = do eoi; err
  <|> do keyword "where"; err
  <|> do col <- Support.column
         if col <= indent
            then err
            else pure ()

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
checkValid (AtPos x) c = if c == x
                            then pure ()
                            else fail "Invalid indentation"
checkValid (AfterPos x) c = if c >= x
                               then pure ()
                               else fail "Invalid indentation"
checkValid EndOfBlock c = fail "End of block"

||| Any token which indicates the end of a statement/block
isTerminator : Token -> Bool
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
atEnd : (indent : IndentInfo) -> EmptyRule ()
atEnd indent
    = eoi
  <|> do nextIs "Expected end of block" (isTerminator . tok)
         pure ()
  <|> do col <- Support.column
         if (col <= indent) 
            then pure ()
            else fail "Not the end of a block entry"

-- Check we're at the end, but only by looking at indentation
export
atEndIndent : (indent : IndentInfo) -> EmptyRule ()
atEndIndent indent
    = eoi
  <|> do col <- Support.column
         if col <= indent
            then pure ()
            else fail "Not the end of a block entry"


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
  <|> do col <- Support.column
         if col <= mincol
            then pure []
            else blockEntries (AtPos col) item

export
blockWithOptHeaderAfter : Int -> (IndentInfo -> Rule hd) -> (IndentInfo -> Rule ty) -> EmptyRule (Maybe hd, List ty)
blockWithOptHeaderAfter {ty} mincol header item
    = do symbol "{"
         commit
         hidt <- optional $ blockEntry AnyIndent header
         restOfBlock hidt
  <|> do col <- Support.column
         if col <= mincol
            then pure (Nothing, [])
            else do hidt <- optional $ blockEntry (AtPos col) header
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
nonEmptyBlock : (IndentInfo -> Rule ty) -> Rule (List ty)
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
