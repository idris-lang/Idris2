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
data Result =
    AString String
  | AUnit
  | ||| arguments: maj min patch tag
    AVersion Nat Nat Nat (Maybe String)
  | ||| arguments: replacement metavariable application
    |||            code for the new top-level lemma
    AMetaVarLemma String String
  | ANameLocList (List (String, FileContext))
  | AHoleList (List HoleData)
  | ANameList (List String)
  | AnOptionList (List REPLOption)

export
SExpable Result where
  toSExp (AString s) = toSExp s
  toSExp (AUnit    ) = toSExp (the (List Int) [])
  toSExp (AVersion
            maj min
            patch
            tag    ) = SExpList [ SExpList (map toSExp [maj, min, patch])
                                , SExpList [StringAtom $ fromMaybe "" tag]
                                ]
  toSExp (AMetaVarLemma app newdef) =
    SExpList [ SymbolAtom "metavariable-lemma"
             , SExpList [ SymbolAtom "replace-metavariable", StringAtom app ]
             , SExpList [ SymbolAtom "definition-type", StringAtom newdef ]
             ]
  toSExp (ANameLocList fcs) = toSExp fcs
  toSExp (AHoleList holes) = toSExp holes
  toSExp (ANameList names) = SExpList (map SymbolAtom names)
  toSExp (AnOptionList opts) = toSExp opts
