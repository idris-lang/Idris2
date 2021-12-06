||| Messages exchanged during the IDE protocol
module Protocol.IDE

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

----------------------------------------------------------------
public export
data Decoration : Type where
  Comment   : Decoration
  Typ       : Decoration
  Function  : Decoration
  Data      : Decoration
  Keyword   : Decoration
  Bound     : Decoration
  Namespace : Decoration
  Postulate : Decoration
  Module    : Decoration

public export
Eq Decoration where
  Comment   == Comment   = True
  Typ       == Typ       = True
  Function  == Function  = True
  Data      == Data      = True
  Keyword   == Keyword   = True
  Bound     == Bound     = True
  Namespace == Namespace = True
  Postulate == Postulate = True
  Module    == Module    = True
  _         == _         = False

-- CAREFUL: this instance is used in SExpable Decoration. If you change
-- it then you need to fix the SExpable implementation in order not to
-- break the IDE mode.
public export
Show Decoration where
  show Comment   = "comment"
  show Typ       = "type"
  show Function  = "function"
  show Data      = "data"
  show Keyword   = "keyword"
  show Bound     = "bound"
  show Namespace = "namespace"
  show Postulate = "postulate"
  show Module    = "module"


------------------------------------------------------------------------
public export
data Formatting : Type where
  Bold      : Formatting
  Italic    : Formatting
  Underline : Formatting

-- CAREFUL: this instance is used in SExpable Formatting. If you change
-- it then you need to fix the SExpable implementation in order not to
-- break the IDE mode.
export
Show Formatting where
  show Bold = "bold"
  show Italic = "italic"
  show Underline = "underline"

-- At most one decoration & one formatting
-- (We could use `These` to guarantee non-emptiness but I am not
-- convinced this will stay being just 2 fields e.g. the emacs mode
-- has support for tagging things as errors, adding links, etc.)
public export
record Properties where
  constructor MkProperties
  decor  : Maybe Decoration
  format : Maybe Formatting

export
mkDecor : Decoration -> Properties
mkDecor dec = MkProperties (Just dec) Nothing

export
mkFormat : Formatting -> Properties
mkFormat = MkProperties Nothing . Just


------------------------------------------------------------------------

{- TODO: refactor ExprSearch to use Hints -}


public export
record Hints where
  constructor MkHints
  list : List String
