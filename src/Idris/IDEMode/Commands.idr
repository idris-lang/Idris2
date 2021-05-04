module Idris.IDEMode.Commands

import Core.Core
import Core.Name
import public Idris.REPL.Opts
import Libraries.Utils.Hex

import System.File

%default total

public export
data SExp = SExpList (List SExp)
          | StringAtom String
          | BoolAtom Bool
          | IntegerAtom Integer
          | SymbolAtom String

public export
data DocMode = Overview | Full

public export
data IDECommand
     = Interpret String
     | LoadFile String (Maybe Integer)
     | TypeOf String (Maybe (Integer, Integer))
     | NameAt String (Maybe (Integer, Integer))
     | CaseSplit Integer Integer String
     | AddClause Integer String
     -- deprecated: | AddProofClause
     | AddMissing Integer String
     | ExprSearch Integer String (List String) Bool
     | ExprSearchNext
     | GenerateDef Integer String
     | GenerateDefNext
     | MakeLemma Integer String
     | MakeCase Integer String
     | MakeWith Integer String
     | DocsFor String (Maybe DocMode)
     | Directive String
     | Apropos String
     | Metavariables Integer
     | WhoCalls String
     | CallsWho String
     | BrowseNamespace String
     | NormaliseTerm     String -- TODO: implement a Binary lib
     | ShowTermImplicits String -- and implement Binary (Term)
     | HideTermImplicits String -- for these four defintions,
     | ElaborateTerm     String -- then change String to Term, as in idris1
     | PrintDefinition String
     | ReplCompletions String
     | EnableSyntax Bool
     | Version
     | GetOptions

readHints : List SExp -> Maybe (List String)
readHints [] = Just []
readHints (StringAtom s :: rest)
    = do rest' <- readHints rest
         pure (s :: rest')
readHints _ = Nothing

export
getIDECommand : SExp -> Maybe IDECommand
getIDECommand (SExpList [SymbolAtom "interpret", StringAtom cmd])
    = Just $ Interpret cmd
getIDECommand (SExpList [SymbolAtom "load-file", StringAtom fname])
    = Just $ LoadFile fname Nothing
getIDECommand (SExpList [SymbolAtom "load-file", StringAtom fname, IntegerAtom l])
    = Just $ LoadFile fname (Just l)
getIDECommand (SExpList [SymbolAtom "type-of", StringAtom n])
    = Just $ TypeOf n Nothing
getIDECommand (SExpList [SymbolAtom "type-of", StringAtom n,
                         IntegerAtom l, IntegerAtom c])
    = Just $ TypeOf n (Just (l, c))
getIDECommand (SExpList [SymbolAtom "name-at", StringAtom n])
    = Just $ NameAt n Nothing
getIDECommand (SExpList [SymbolAtom "name-at", StringAtom n,
                         IntegerAtom l, IntegerAtom c])
    = Just $ NameAt n (Just (l, c))
getIDECommand (SExpList [SymbolAtom "case-split", IntegerAtom l, IntegerAtom c,
                         StringAtom n])
    = Just $ CaseSplit l c n
getIDECommand (SExpList [SymbolAtom "case-split", IntegerAtom l, StringAtom n])
    = Just $ CaseSplit l 0 n
getIDECommand (SExpList [SymbolAtom "add-clause", IntegerAtom l, StringAtom n])
    = Just $ AddClause l n
getIDECommand (SExpList [SymbolAtom "add-missing", IntegerAtom line, StringAtom n])
    = Just $ AddMissing line n
getIDECommand (SExpList [SymbolAtom "proof-search", IntegerAtom l, StringAtom n])
    = Just $ ExprSearch l n [] False
getIDECommand (SExpList [SymbolAtom "proof-search", IntegerAtom l, StringAtom n, SExpList hs])
    = case readHints hs of
           Just hs' => Just $ ExprSearch l n hs' False
           _ => Nothing
getIDECommand (SExpList [SymbolAtom "proof-search", IntegerAtom l, StringAtom n, SExpList hs, SymbolAtom mode])
    = case readHints hs of
           Just hs' => Just $ ExprSearch l n hs' (getMode mode)
           _ => Nothing
  where
    getMode : String -> Bool
    getMode m = m == "all"
getIDECommand (SymbolAtom "proof-search-next") = Just ExprSearchNext
getIDECommand (SExpList [SymbolAtom "generate-def", IntegerAtom l, StringAtom n])
    = Just $ GenerateDef l n
getIDECommand (SymbolAtom "generate-def-next") = Just GenerateDefNext
getIDECommand (SExpList [SymbolAtom "make-lemma", IntegerAtom l, StringAtom n])
    = Just $ MakeLemma l n
getIDECommand (SExpList [SymbolAtom "make-case", IntegerAtom l, StringAtom n])
    = Just $ MakeCase l n
getIDECommand (SExpList [SymbolAtom "make-with", IntegerAtom l, StringAtom n])
    = Just $ MakeWith l n
getIDECommand (SExpList (SymbolAtom "docs-for" ::  StringAtom n :: modeTail))
    = do -- Maybe monad
         modeOpt <- case modeTail of
                      []                      => Just Nothing
                      [SymbolAtom "overview"] => Just $ Just Overview
                      [SymbolAtom "full"    ] => Just $ Just Full
                      _ => Nothing
         Just $ DocsFor n modeOpt
getIDECommand (SExpList [SymbolAtom "apropos", StringAtom n])
    = Just $ Apropos n
getIDECommand (SExpList [SymbolAtom "directive", StringAtom n])
    = Just $ Directive n
getIDECommand (SExpList [SymbolAtom "metavariables", IntegerAtom n])
    = Just $ Metavariables n
getIDECommand (SExpList [SymbolAtom "who-calls", StringAtom n])
    = Just $ WhoCalls n
getIDECommand (SExpList [SymbolAtom "calls-who", StringAtom n])
    = Just $ CallsWho n
getIDECommand (SExpList [SymbolAtom "browse-namespace", StringAtom ns])
    = Just $ BrowseNamespace ns
getIDECommand (SExpList [SymbolAtom "normalise-term", StringAtom tm])
    = Just $ NormaliseTerm     tm
getIDECommand (SExpList [SymbolAtom "show-term-implicits", StringAtom tm])
    = Just $ ShowTermImplicits tm
getIDECommand (SExpList [SymbolAtom "hide-term-implicits", StringAtom tm])
    = Just $ HideTermImplicits tm
getIDECommand (SExpList [SymbolAtom "elaborate-term", StringAtom tm])
    = Just $ ElaborateTerm     tm
getIDECommand (SExpList [SymbolAtom "print-definition", StringAtom n])
    = Just $ PrintDefinition n
getIDECommand (SExpList [SymbolAtom "repl-completions", StringAtom n])
    = Just $ ReplCompletions n
getIDECommand (SExpList [SymbolAtom "enable-syntax", BoolAtom b])
    = Just $ EnableSyntax b
getIDECommand (SymbolAtom "version") = Just Version
getIDECommand (SExpList [SymbolAtom "get-options"]) = Just GetOptions
getIDECommand _ = Nothing

export
putIDECommand : IDECommand -> SExp
putIDECommand (Interpret cmd)                 = (SExpList [SymbolAtom "interpret", StringAtom cmd])
putIDECommand (LoadFile fname Nothing)        = (SExpList [SymbolAtom "load-file", StringAtom fname])
putIDECommand (LoadFile fname (Just line))    = (SExpList [SymbolAtom "load-file", StringAtom fname, IntegerAtom line])
putIDECommand (TypeOf cmd Nothing)            = (SExpList [SymbolAtom "type-of", StringAtom cmd])
putIDECommand (TypeOf cmd (Just (line, col))) = (SExpList [SymbolAtom "type-of", StringAtom cmd, IntegerAtom line, IntegerAtom col])
putIDECommand (NameAt cmd Nothing)            = (SExpList [SymbolAtom "name-at", StringAtom cmd])
putIDECommand (NameAt cmd (Just (line, col))) = (SExpList [SymbolAtom "name-at", StringAtom cmd, IntegerAtom line, IntegerAtom col])
putIDECommand (CaseSplit line col n)          = (SExpList [SymbolAtom "case-split", IntegerAtom line, IntegerAtom col, StringAtom n])
putIDECommand (AddClause line n)              = (SExpList [SymbolAtom "add-clause", IntegerAtom line, StringAtom n])
putIDECommand (AddMissing line n)             = (SExpList [SymbolAtom "add-missing", IntegerAtom line, StringAtom n])
putIDECommand (ExprSearch line n exprs mode)  = (SExpList [SymbolAtom "proof-search", IntegerAtom line, StringAtom n, SExpList $ map StringAtom exprs, getMode mode])
  where
  getMode : Bool -> SExp
  getMode True  = SymbolAtom "all"
  getMode False = SymbolAtom "other"
putIDECommand ExprSearchNext                  = SymbolAtom "proof-search-next"
putIDECommand (GenerateDef line n)            = (SExpList [SymbolAtom "generate-def", IntegerAtom line, StringAtom n])
putIDECommand GenerateDefNext                 = SymbolAtom "generate-def-next"
putIDECommand (MakeLemma line n)              = (SExpList [SymbolAtom "make-lemma", IntegerAtom line, StringAtom n])
putIDECommand (MakeCase line n)               = (SExpList [SymbolAtom "make-case", IntegerAtom line, StringAtom n])
putIDECommand (MakeWith line n)               = (SExpList [SymbolAtom "make-with", IntegerAtom line, StringAtom n])
putIDECommand (DocsFor n modeOpt)             = let modeTail = case modeOpt of
                                                                 Nothing       => []
                                                                 Just Overview => [SymbolAtom "overview"]
                                                                 Just Full     => [SymbolAtom "full"] in
                                                (SExpList (SymbolAtom "docs-for" ::  StringAtom n :: modeTail))
putIDECommand (Apropos n)                     = (SExpList [SymbolAtom "apropos", StringAtom n])
putIDECommand (Metavariables n)               = (SExpList [SymbolAtom "metavariables", IntegerAtom n])
putIDECommand (WhoCalls n)                    = (SExpList [SymbolAtom "who-calls", StringAtom n])
putIDECommand (CallsWho n)                    = (SExpList [SymbolAtom "calls-who", StringAtom n])
putIDECommand (BrowseNamespace ns)            = (SExpList [SymbolAtom "browse-namespace", StringAtom ns])
putIDECommand (NormaliseTerm     tm)          = (SExpList [SymbolAtom "normalise-term", StringAtom tm])
putIDECommand (ShowTermImplicits tm)          = (SExpList [SymbolAtom "show-term-implicits", StringAtom tm])
putIDECommand (HideTermImplicits tm)          = (SExpList [SymbolAtom "hide-term-implicits", StringAtom tm])
putIDECommand (ElaborateTerm     tm)          = (SExpList [SymbolAtom "elaborate-term", StringAtom tm])
putIDECommand (PrintDefinition n)             = (SExpList [SymbolAtom "print-definition", StringAtom n])
putIDECommand (ReplCompletions n)             = (SExpList [SymbolAtom "repl-completions", StringAtom n])
putIDECommand (Directive n)             = (SExpList [SymbolAtom "directive", StringAtom n])
putIDECommand (EnableSyntax b)                = (SExpList [SymbolAtom "enable-syntax", BoolAtom b])
putIDECommand GetOptions                      = (SExpList [SymbolAtom "get-options"])
putIDECommand Version                         = SymbolAtom "version"

export
getMsg : SExp -> Maybe (IDECommand, Integer)
getMsg (SExpList [cmdexp, IntegerAtom num])
   = do cmd <- getIDECommand cmdexp
        pure (cmd, num)
getMsg _ = Nothing

escape : String -> String
escape = pack . concatMap escapeChar . unpack
  where
    escapeChar : Char -> List Char
    escapeChar '\\' = ['\\', '\\']
    escapeChar '"'  = ['\\', '\"']
    escapeChar c    = [c]

export
Show SExp where
  show (SExpList xs) = assert_total $ "(" ++ showSep " " (map show xs) ++ ")"
  show (StringAtom str) = "\"" ++ escape str ++ "\""
  show (BoolAtom b) = ":" ++ show b
  show (IntegerAtom i) = show i
  show (SymbolAtom s) = ":" ++ s

public export
interface SExpable a where
  toSExp : a -> SExp

export
SExpable IDECommand where
  toSExp = putIDECommand

export
SExpable SExp where
  toSExp = id

export
SExpable Bool where
  toSExp = BoolAtom

export
SExpable String where
  toSExp = StringAtom

export
SExpable Integer where
  toSExp = IntegerAtom

export
SExpable Int where
  toSExp = IntegerAtom . cast

export
SExpable Nat where
  toSExp = IntegerAtom . cast

export
SExpable Name where
  toSExp = SymbolAtom . show

export
(SExpable a, SExpable b) => SExpable (a, b) where
  toSExp (x, y)
      = case toSExp y of
             SExpList xs => SExpList (toSExp x :: xs)
             y' => SExpList [toSExp x, y']

export
SExpable a => SExpable (List a) where
  toSExp xs
      = SExpList (map toSExp xs)

export
SExpable a => SExpable (Maybe a) where
  toSExp Nothing = SExpList []
  toSExp (Just x) = toSExp x

export
sym : String -> Name
sym = UN

export
version : Int -> Int -> SExp
version maj min = toSExp (SymbolAtom "protocol-version", maj, min)

sendStr : File -> String -> IO ()
sendStr f st =
  map (const ()) (fPutStr f st)

export
send : SExpable a => File -> a -> Core ()
send f resp
    = do let r = show (toSExp resp) ++ "\n"
         coreLift $ sendStr f $ leftPad '0' 6 (asHex (cast (length r)))
         coreLift $ sendStr f r
         coreLift $ fflush f
