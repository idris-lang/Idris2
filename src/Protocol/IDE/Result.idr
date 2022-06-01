module Protocol.IDE.Result

import Protocol.SExp

import Protocol.IDE.Holes
import Protocol.IDE.FileContext

import Data.List1
import Data.Maybe

%default total

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

export
FromSExpable REPLOption where
  fromSExp (SExpList
    [ SymbolAtom name
    , val
    ]) = do
    let Nothing = fromSExp val
      | Just val => Just $ MkOption {name, type = BOOL, val}
    let Nothing = fromSExp val
      | Just val => Just $ MkOption {name, type = STRING, val}
    val <- fromSExp val
    Just $ MkOption {name, type = ATOM, val}
  fromSExp _ = Nothing

public export
record MetaVarLemma where
  constructor MkMetaVarLemma
  application, lemma : String

export
SExpable MetaVarLemma where
  toSExp mvl = SExpList [ SymbolAtom "metavariable-lemma"
             , SExpList [ SymbolAtom "replace-metavariable", StringAtom mvl.application ]
             , SExpList [ SymbolAtom "definition-type", StringAtom mvl.lemma ]
             ]

export
FromSExpable MetaVarLemma where
  fromSExp (SExpList [ SymbolAtom "metavariable-lemma"
            , SExpList [ SymbolAtom "replace-metavariable", StringAtom application ]
            , SExpList [ SymbolAtom "definition-type", StringAtom lemma ]
            ]) = Just $ MkMetaVarLemma {application, lemma}
  fromSExp _ = Nothing

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
FromSExpable IdrisVersion where
  fromSExp (SExpList
    [ SExpList [majorSExp, minorSExp, patchSExp]
    , SExpList [StringAtom tagSExp]
    ]) = do pure $ MkIdrisVersion
              { major = !(fromSExp majorSExp)
              , minor = !(fromSExp minorSExp)
              , patch = !(fromSExp patchSExp)
              , tag = case tagSExp of
                  "" => Nothing
                  str => Just str}
  fromSExp _ = Nothing

public export
data Result =
    AString String
  | AUnit
  | AVersion IdrisVersion
  | AMetaVarLemma MetaVarLemma
  | ANameLocList (List (String, FileContext))
  | AHoleList (List HoleData)
  | ACompletionList (List String) String
  | ANameList (List String)
  | AnOptionList (List REPLOption)
  | AnIntroList (List1 String)

export
SExpable Result where
  toSExp (AString s) = toSExp s
  toSExp (AUnit    ) = toSExp (the (List Int) [])
  toSExp (AVersion version) = toSExp version
  toSExp (AMetaVarLemma mvl) = toSExp mvl
  toSExp (ANameLocList fcs) = toSExp fcs
  toSExp (AHoleList holes) = toSExp holes
  toSExp (ANameList names) = SExpList (map StringAtom names)
  toSExp (ACompletionList names str) = SExpList [SExpList (map StringAtom names), StringAtom str]
  toSExp (AnOptionList opts) = toSExp opts
  toSExp (AnIntroList iss) = toSExp iss

-- This code is not efficient. Usually the client knows what kind of
-- result to expect based on the request it issued.
export
FromSExpable Result where
  fromSExp (SExpList []) = Just AUnit -- resolve ambiguity somewhat arbitrarily...
  fromSExp sexp = do
  let Nothing = fromSExp sexp
    | Just str => pure $ AString str
  let Nothing = fromSExp sexp
    | Just version => pure $ AVersion version
  let Nothing = fromSExp sexp
    | Just mvl => pure $ AMetaVarLemma mvl
  let Nothing = fromSExp sexp
    | Just nll => pure $ ANameLocList nll
  let Nothing = fromSExp sexp
    | Just hl => pure $ AHoleList hl
  let Nothing = fromSExp sexp
    | Just nl => pure $ ANameList nl
  let Nothing = fromSExp sexp
    | Just nlr => pure $ uncurry ACompletionList nlr
  let Nothing = fromSExp sexp
    | Just optl => pure $ AnOptionList optl
  let Nothing = fromSExp sexp
    | Just optl => pure $ AnIntroList optl
  Nothing
