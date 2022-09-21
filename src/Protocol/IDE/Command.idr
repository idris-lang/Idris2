module Protocol.IDE.Command
import Protocol.SExp

%default total

-- TODO: introduce SExpable DocMode and refactor below to use it
public export
data DocMode = Overview | Full

public export
record Hints where
  constructor MkHints
  list : List String

export
SExpable Hints where
  toSExp hs = toSExp hs.list

export
FromSExpable Hints where
  fromSExp hs = MkHints <$> fromSExp hs

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
     | Intro Integer String -- line, hole name
     | Refine Integer String String -- line, hole name, expression
     | ExprSearch Integer String Hints Bool
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
    = Just $ ExprSearch l n (MkHints []) False
getIDECommand (SExpList [SymbolAtom "intro", IntegerAtom l, StringAtom h])
    = Just $ Intro l h
getIDECommand (SExpList [SymbolAtom "refine", IntegerAtom l, StringAtom h, StringAtom n])
    = Just $ Refine l h n
getIDECommand (SExpList [SymbolAtom "proof-search", IntegerAtom l, StringAtom n, hs])
    = (\hs' => ExprSearch l n hs' False) <$> fromSExp hs
getIDECommand (SExpList [SymbolAtom "proof-search", IntegerAtom l, StringAtom n, hs, SymbolAtom mode])
    = (\hs' => ExprSearch l n hs' (getMode mode)) <$> fromSExp hs
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
FromSExpable IDECommand where
  fromSExp = getIDECommand

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
putIDECommand (Intro line hole)               = (SExpList [SymbolAtom "intro", IntegerAtom line, StringAtom hole])
putIDECommand (Refine line hole name)         = (SExpList [SymbolAtom "refine", IntegerAtom line, StringAtom hole, StringAtom name])
putIDECommand (ExprSearch line n hints mode)  = (SExpList [SymbolAtom "proof-search", IntegerAtom line, StringAtom n, toSExp hints, getMode mode])
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
SExpable IDECommand where
  toSExp = putIDECommand
