module Protocol.IDE.Result

import Protocol.SExp

import Protocol.IDE.Holes
import Protocol.IDE.FileContext

import Data.Maybe

public export
data OptionType = BOOL | STRING | ATOM

public export
(.sem) : OptionType -> Type
BOOL   .sem = Bool
STRING .sem = String
ATOM   .sem = String

%unbound_implicits off
public export
record REPLOption where
  constructor MkOption
  name : String
  type : OptionType
  val  : type.sem
%unbound_implicits on

sexpOptionVal : {type : OptionType} -> type.sem -> SExp
sexpOptionVal {type = BOOL  } = toSExp
sexpOptionVal {type = STRING} = toSExp
sexpOptionVal {type = ATOM  } = toSExp

export
SExpable REPLOption where
  toSExp opt@(MkOption {}) = SExpList
    [ SymbolAtom opt.name
    , sexpOptionVal opt.val
    ]

public export
record MetaVarLemma where
  constructor MkMetaVarLemma
  application, lemma : String

public export
record IdrisVersion where
  constructor MkIdrisVersion
  major, minor, patch : Nat
  tag : Maybe String

export
SExpable IdrisVersion where
  toSExp version = SExpList
    [ SExpList (map toSExp [version.major, version.minor, version.patch])
    , SExpList [StringAtom $ fromMaybe "" version.tag]
    ]

export
SExpable MetaVarLemma where
  toSExp mvl =  SExpList [ SymbolAtom "metavariable-lemma"
             , SExpList [ SymbolAtom "replace-metavariable", StringAtom mvl.application ]
             , SExpList [ SymbolAtom "definition-type", StringAtom mvl.lemma ]
             ]

public export
data Result =
    AString String
  | AUnit
  | AVersion IdrisVersion
  | AMetaVarLemma MetaVarLemma
  | ANameLocList (List (String, FileContext))
  | AHoleList (List HoleData)
  | ANameList (List String)
  | AnOptionList (List REPLOption)

export
SExpable Result where
  toSExp (AString s) = toSExp s
  toSExp (AUnit    ) = toSExp (the (List Int) [])
  toSExp (AVersion version) = toSExp version
  toSExp (AMetaVarLemma mvl) = toSExp mvl
  toSExp (ANameLocList fcs) = toSExp fcs
  toSExp (AHoleList holes) = toSExp holes
  toSExp (ANameList names) = SExpList (map SymbolAtom names)
  toSExp (AnOptionList opts) = toSExp opts
