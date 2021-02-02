module Idris.IDEMode.SyntaxHighlight

import Core.Context
import Core.InitPrimitives
import Core.Metadata
import Core.TT

import Idris.REPL
import Idris.IDEMode.Commands

import Data.List

%default covering

data Decoration : Type where
  Typ : Decoration
  Function : Decoration
  Data : Decoration
  Keyword : Decoration
  Bound : Decoration

SExpable Decoration where
  toSExp Typ = SymbolAtom "type"
  toSExp Function = SymbolAtom "function"
  toSExp Data = SymbolAtom "data"
  toSExp Keyword = SymbolAtom "keyword"
  toSExp Bound = SymbolAtom "bound"

record Highlight where
  constructor MkHighlight
  location : FC
  name : Name
  isImplicit : Bool
  key : String
  decor : Decoration
  docOverview : String
  typ : String
  ns : String

SExpable FC where
  toSExp (MkFC fname (startLine, startCol) (endLine, endCol))
    = SExpList [ SExpList [ SymbolAtom "filename", StringAtom fname ]
               , SExpList [ SymbolAtom "start", IntegerAtom (cast startLine + 1), IntegerAtom (cast startCol + 1) ]
               , SExpList [ SymbolAtom "end", IntegerAtom (cast endLine + 1), IntegerAtom (cast endCol + 1) ]
               ]
  toSExp EmptyFC = SExpList []

SExpable Highlight where
  toSExp (MkHighlight loc nam impl k dec doc t ns)
    = SExpList [ toSExp loc
               , SExpList [ SExpList [ SymbolAtom "name", StringAtom (show nam) ]
                          , SExpList [ SymbolAtom "namespace", StringAtom ns ]
                          , SExpList [ SymbolAtom "decor", toSExp dec ]
                          , SExpList [ SymbolAtom "implicit", toSExp impl ]
                          , SExpList [ SymbolAtom "key", StringAtom k ]
                          , SExpList [ SymbolAtom "doc-overview", StringAtom doc ]
                          , SExpList [ SymbolAtom "type", StringAtom t ]
                          ]
               ]

inFile : String -> (FC, (Name, Nat, ClosedTerm)) -> Bool
inFile fname (MkFC file _ _, _) = file == fname
inFile _     (EmptyFC, _)       = False

||| Output some data using current dialog index
export
printOutput : {auto o : Ref ROpts REPLOpts} ->
              SExp -> Core ()
printOutput msg
  =  do opts <- get ROpts
        case idemode opts of
          REPL _ => pure ()
          IDEMode i _ f =>
            send f (SExpList [SymbolAtom "output",
                              msg, toSExp i])


outputHighlight : {auto opts : Ref ROpts REPLOpts} ->
                  Highlight -> Core ()
outputHighlight h =
  printOutput $ SExpList [ SymbolAtom "ok"
                         , SExpList [ SymbolAtom "highlight-source"
                                    , toSExp hlt
                                    ]
                         ]
  where
    hlt : List Highlight
    hlt = [h]

outputNameSyntax : {auto opts : Ref ROpts REPLOpts} ->
                   (FC, (Name, Nat, ClosedTerm)) -> Core ()
outputNameSyntax (fc, (name, _, term)) =
  let dec = case term of
                 (Local fc x idx y) => Just Bound

                 -- See definition of NameType in Core.TT for possible values of Ref's nametype field
                 -- data NameType : Type where
                 -- Bound   : NameType
                 -- Func    : NameType
                 -- DataCon : (tag : Int) -> (arity : Nat) -> NameType
                 -- TyCon   : (tag : Int) -> (arity : Nat) -> NameType
                 (Ref fc Bound name) => Just Bound
                 (Ref fc Func name) => Just Function
                 (Ref fc (DataCon tag arity) name) => Just Data
                 (Ref fc (TyCon tag arity) name) => Just Typ
                 (Meta fc x y xs) => Just Bound
                 (Bind fc x b scope) => Just Bound
                 (App fc fn arg) => Just Bound
                 (As fc x as pat) => Just Bound
                 (TDelayed fc x y) => Nothing
                 (TDelay fc x ty arg) => Nothing
                 (TForce fc x y) => Nothing
                 (PrimVal fc c) => Just Typ
                 (Erased fc imp) => Just Bound
                 (TType fc) => Just Typ
      hilite = Prelude.map (\ d => MkHighlight fc name False "" d "" (show term) "") dec
  in maybe (pure ()) outputHighlight hilite

export
outputSyntaxHighlighting : {auto m : Ref MD Metadata} ->
                           {auto opts : Ref ROpts REPLOpts} ->
                           String ->
                           REPLResult ->
                           Core REPLResult
outputSyntaxHighlighting fname loadResult = do
  opts <- get ROpts
  when (opts.synHighlightOn) $ do
    allNames <- filter (inFile fname) . names <$> get MD
    --  decls <- filter (inFile fname) . tydecls <$> get MD
    _ <- traverse outputNameSyntax allNames -- ++ decls)
    pure ()
  pure loadResult
