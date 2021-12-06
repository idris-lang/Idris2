module Idris.Syntax

import public Core.Binary
import public Core.Context
import public Core.Context.Log
import public Core.Core
import public Core.FC
import public Core.Normalise
import public Core.Options
import public Core.TTC
import public Core.TT

import TTImp.TTImp

import Libraries.Data.ANameMap
import Data.List
import Data.SnocList
import Data.Maybe
import Libraries.Data.NameMap
import Libraries.Data.SortedMap
import Libraries.Data.String.Extra
import Libraries.Data.StringMap
import Libraries.Text.PrettyPrint.Prettyprinter

import Parser.Lexer.Source

%default covering

public export
data Fixity = InfixL | InfixR | Infix | Prefix

export
Show Fixity where
  show InfixL = "infixl"
  show InfixR = "infixr"
  show Infix  = "infix"
  show Prefix = "prefix"

public export
OpStr' : Type -> Type
OpStr' nm = nm

public export
OpStr : Type
OpStr = OpStr' Name

mutual

  ||| Source language as produced by the parser
  public export
  PTerm : Type
  PTerm = PTerm' Name

  ||| Internal PTerm
  ||| Source language as produced by the unelaboration of core Terms
  ||| KindedNames carry extra information about the nature of the variable
  public export
  IPTerm : Type
  IPTerm = PTerm' KindedName

  ||| The full high level source language
  ||| This gets desugared to RawImp (TTImp.TTImp),
  ||| then elaborated to Term (Core.TT)
  public export
  data PTerm' : Type -> Type where
       -- Direct (more or less) translations to RawImp

       PRef : FC -> nm -> PTerm' nm
       PPi : FC -> RigCount -> PiInfo (PTerm' nm) -> Maybe Name ->
             (argTy : PTerm' nm) -> (retTy : PTerm' nm) -> PTerm' nm
       PLam : FC -> RigCount -> PiInfo (PTerm' nm) -> PTerm' nm ->
              (argTy : PTerm' nm) -> (scope : PTerm' nm) -> PTerm' nm
       PLet : FC -> RigCount -> (pat : PTerm' nm) ->
              (nTy : PTerm' nm) -> (nVal : PTerm' nm) -> (scope : PTerm' nm) ->
              (alts : List (PClause' nm)) -> PTerm' nm
       PCase : FC -> PTerm' nm -> List (PClause' nm) -> PTerm' nm
       PLocal : FC -> List (PDecl' nm) -> (scope : PTerm' nm) -> PTerm' nm
       PUpdate : FC -> List (PFieldUpdate' nm) -> PTerm' nm
       PApp : FC -> PTerm' nm -> PTerm' nm -> PTerm' nm
       PWithApp : FC -> PTerm' nm -> PTerm' nm -> PTerm' nm
       PNamedApp : FC -> PTerm' nm -> Name -> PTerm' nm -> PTerm' nm
       PAutoApp : FC -> PTerm' nm -> PTerm' nm -> PTerm' nm

       PDelayed : FC -> LazyReason -> PTerm' nm -> PTerm' nm
       PDelay : FC -> PTerm' nm -> PTerm' nm
       PForce : FC -> PTerm' nm -> PTerm' nm

       PSearch : FC -> (depth : Nat) -> PTerm' nm
       PPrimVal : FC -> Constant -> PTerm' nm
       PQuote : FC -> PTerm' nm -> PTerm' nm
       PQuoteName : FC -> Name -> PTerm' nm
       PQuoteDecl : FC -> List (PDecl' nm) -> PTerm' nm
       PUnquote : FC -> PTerm' nm -> PTerm' nm
       PRunElab : FC -> PTerm' nm -> PTerm' nm
       PHole : FC -> (bracket : Bool) -> (holename : String) -> PTerm' nm
       PType : FC -> PTerm' nm
       PAs : FC -> (nameFC : FC) -> Name -> (pattern : PTerm' nm) -> PTerm' nm
       PDotted : FC -> PTerm' nm -> PTerm' nm
       PImplicit : FC -> PTerm' nm
       PInfer : FC -> PTerm' nm

       -- Operators

       POp : (full, opFC : FC) -> OpStr' nm -> PTerm' nm -> PTerm' nm -> PTerm' nm
       PPrefixOp : (full, opFC : FC) -> OpStr' nm -> PTerm' nm -> PTerm' nm
       PSectionL : (full, opFC : FC) -> OpStr' nm -> PTerm' nm -> PTerm' nm
       PSectionR : (full, opFC : FC) -> PTerm' nm -> OpStr' nm -> PTerm' nm
       PEq : FC -> PTerm' nm -> PTerm' nm -> PTerm' nm
       PBracketed : FC -> PTerm' nm -> PTerm' nm

       -- Syntactic sugar
       PString : FC -> List (PStr' nm) -> PTerm' nm
       PMultiline : FC -> (indent : Nat) -> List (List (PStr' nm)) -> PTerm' nm
       PDoBlock : FC -> Maybe Namespace -> List (PDo' nm) -> PTerm' nm
       PBang : FC -> PTerm' nm -> PTerm' nm
       PIdiom : FC -> PTerm' nm -> PTerm' nm
       PList : (full, nilFC : FC) -> List (FC, PTerm' nm) -> PTerm' nm
                                        -- ^   v location of the conses/snocs
       PSnocList : (full, nilFC : FC) -> SnocList ((FC, PTerm' nm)) -> PTerm' nm
       PPair : FC -> PTerm' nm -> PTerm' nm -> PTerm' nm
       PDPair : (full, opFC : FC) -> PTerm' nm -> PTerm' nm -> PTerm' nm -> PTerm' nm
       PUnit : FC -> PTerm' nm
       PIfThenElse : FC -> PTerm' nm -> PTerm' nm -> PTerm' nm -> PTerm' nm
       PComprehension : FC -> PTerm' nm -> List (PDo' nm) -> PTerm' nm
       PRewrite : FC -> PTerm' nm -> PTerm' nm -> PTerm' nm
       -- A list range  [x,y..z]
       PRange : FC -> PTerm' nm -> Maybe (PTerm' nm) -> PTerm' nm -> PTerm' nm
       -- A stream range [x,y..]
       PRangeStream : FC -> PTerm' nm -> Maybe (PTerm' nm) -> PTerm' nm
       -- r.x.y
       PPostfixApp : FC -> PTerm' nm -> List (FC, Name) -> PTerm' nm
       -- .x.y
       PPostfixAppPartial : FC -> List (FC, Name) -> PTerm' nm

       -- Debugging
       PUnifyLog : FC -> LogLevel -> PTerm' nm -> PTerm' nm

       -- with-disambiguation
       PWithUnambigNames : FC -> List Name -> PTerm' nm -> PTerm' nm

  export
  getPTermLoc : PTerm' nm -> FC
  getPTermLoc (PRef fc _) = fc
  getPTermLoc (PPi fc _ _ _ _ _) = fc
  getPTermLoc (PLam fc _ _ _ _ _) = fc
  getPTermLoc (PLet fc _ _ _ _ _ _) = fc
  getPTermLoc (PCase fc _ _) = fc
  getPTermLoc (PLocal fc _ _) = fc
  getPTermLoc (PUpdate fc _) = fc
  getPTermLoc (PApp fc _ _) = fc
  getPTermLoc (PWithApp fc _ _) = fc
  getPTermLoc (PAutoApp fc _ _) = fc
  getPTermLoc (PNamedApp fc _ _ _) = fc
  getPTermLoc (PDelayed fc _ _) = fc
  getPTermLoc (PDelay fc _) = fc
  getPTermLoc (PForce fc _) = fc
  getPTermLoc (PSearch fc _) = fc
  getPTermLoc (PPrimVal fc _) = fc
  getPTermLoc (PQuote fc _) = fc
  getPTermLoc (PQuoteName fc _) = fc
  getPTermLoc (PQuoteDecl fc _) = fc
  getPTermLoc (PUnquote fc _) = fc
  getPTermLoc (PRunElab fc _) = fc
  getPTermLoc (PHole fc _ _) = fc
  getPTermLoc (PType fc) = fc
  getPTermLoc (PAs fc _  _ _) = fc
  getPTermLoc (PDotted fc _) = fc
  getPTermLoc (PImplicit fc) = fc
  getPTermLoc (PInfer fc) = fc
  getPTermLoc (POp fc _ _ _ _) = fc
  getPTermLoc (PPrefixOp fc _ _ _) = fc
  getPTermLoc (PSectionL fc _ _ _) = fc
  getPTermLoc (PSectionR fc _ _ _) = fc
  getPTermLoc (PEq fc _ _) = fc
  getPTermLoc (PBracketed fc _) = fc
  getPTermLoc (PString fc _) = fc
  getPTermLoc (PMultiline fc _ _) = fc
  getPTermLoc (PDoBlock fc _ _) = fc
  getPTermLoc (PBang fc _) = fc
  getPTermLoc (PIdiom fc _) = fc
  getPTermLoc (PList fc _ _) = fc
  getPTermLoc (PSnocList fc _ _) = fc
  getPTermLoc (PPair fc _ _) = fc
  getPTermLoc (PDPair fc _ _ _ _) = fc
  getPTermLoc (PUnit fc) = fc
  getPTermLoc (PIfThenElse fc _ _ _) = fc
  getPTermLoc (PComprehension fc _ _) = fc
  getPTermLoc (PRewrite fc _ _) = fc
  getPTermLoc (PRange fc _ _ _) = fc
  getPTermLoc (PRangeStream fc _ _) = fc
  getPTermLoc (PPostfixApp fc _ _) = fc
  getPTermLoc (PPostfixAppPartial fc _) = fc
  getPTermLoc (PUnifyLog fc _ _) = fc
  getPTermLoc (PWithUnambigNames fc _ _) = fc

  public export
  PFieldUpdate : Type
  PFieldUpdate = PFieldUpdate' Name

  public export
  data PFieldUpdate' : Type -> Type where
       PSetField : (path : List String) -> PTerm' nm -> PFieldUpdate' nm
       PSetFieldApp : (path : List String) -> PTerm' nm -> PFieldUpdate' nm

  public export
  PDo : Type
  PDo = PDo' Name

  public export
  data PDo' : Type -> Type where
       DoExp : FC -> PTerm' nm -> PDo' nm
       DoBind : FC -> (nameFC : FC) -> Name -> PTerm' nm -> PDo' nm
       DoBindPat : FC -> PTerm' nm -> PTerm' nm -> List (PClause' nm) -> PDo' nm
       DoLet : FC -> (lhs : FC) -> Name -> RigCount -> PTerm' nm -> PTerm' nm -> PDo' nm
       DoLetPat : FC -> PTerm' nm -> PTerm' nm -> PTerm' nm -> List (PClause' nm) -> PDo' nm
       DoLetLocal : FC -> List (PDecl' nm) -> PDo' nm
       DoRewrite : FC -> PTerm' nm -> PDo' nm

  public export
  PStr : Type
  PStr = PStr' Name

  public export
  data PStr' : Type -> Type where
       StrLiteral : FC -> String -> PStr' nm
       StrInterp : FC -> PTerm' nm -> PStr' nm

  export
  getLoc : PDo' nm -> FC
  getLoc (DoExp fc _) = fc
  getLoc (DoBind fc _ _ _) = fc
  getLoc (DoBindPat fc _ _ _) = fc
  getLoc (DoLet fc _ _ _ _ _) = fc
  getLoc (DoLetPat fc _ _ _ _) = fc
  getLoc (DoLetLocal fc _) = fc
  getLoc (DoRewrite fc _) = fc

  export
  papply : FC -> PTerm' nm -> List (PTerm' nm) -> PTerm' nm
  papply fc f [] = f
  papply fc f (a :: as) = papply fc (PApp fc f a) as

  export
  applyArgs : PTerm' nm -> List (FC, PTerm' nm) -> PTerm' nm
  applyArgs f [] = f
  applyArgs f ((fc, a) :: args) = applyArgs (PApp fc f a) args

  public export
  PTypeDecl : Type
  PTypeDecl = PTypeDecl' Name

  public export
  data PTypeDecl' : Type -> Type where
       MkPTy : FC -> (nameFC : FC) -> (n : Name) ->
               (doc: String) -> (type : PTerm' nm) -> PTypeDecl' nm

  export
  getPTypeDeclLoc : PTypeDecl' nm -> FC
  getPTypeDeclLoc (MkPTy fc _ _ _ _) = fc

  public export
  PDataDecl : Type
  PDataDecl = PDataDecl' Name

  public export
  data PDataDecl' : Type -> Type where
       MkPData : FC -> (tyname : Name) -> (tycon : PTerm' nm) ->
                 (opts : List DataOpt) ->
                 (datacons : List (PTypeDecl' nm)) -> PDataDecl' nm
       MkPLater : FC -> (tyname : Name) -> (tycon : PTerm' nm) -> PDataDecl' nm

  export
  addDataOpt : DataOpt -> PDataDecl' a -> PDataDecl' a
  addDataOpt opt (MkPData fc tyname tycon       opts  datacons) =
                  MkPData fc tyname tycon (opt::opts) datacons
  addDataOpt opt later@(MkPLater _ _ _) = later

  export
  getPDataDeclLoc : PDataDecl' nm -> FC
  getPDataDeclLoc (MkPData fc _ _ _ _) = fc
  getPDataDeclLoc (MkPLater fc _ _) = fc

  public export
  PClause : Type
  PClause = PClause' Name

  public export
  data PClause' : Type -> Type where
       MkPatClause : FC -> (lhs : PTerm' nm) -> (rhs : PTerm' nm) ->
                     (whereblock : List (PDecl' nm)) -> PClause' nm
       MkWithClause : FC -> (lhs : PTerm' nm) ->
                      (wval : PTerm' nm) -> (prf : Maybe Name) ->
                      List WithFlag -> List (PClause' nm) -> PClause' nm
       MkImpossible : FC -> (lhs : PTerm' nm) -> PClause' nm

  export
  getPClauseLoc : PClause -> FC
  getPClauseLoc (MkPatClause fc _ _ _) = fc
  getPClauseLoc (MkWithClause fc _ _ _ _ _) = fc
  getPClauseLoc (MkImpossible fc _) = fc

  public export
  data Directive : Type where
       Hide : Name -> Directive
       Logging : Maybe LogLevel -> Directive
       LazyOn : Bool -> Directive
       UnboundImplicits : Bool -> Directive
       AmbigDepth : Nat -> Directive
       PairNames : Name -> Name -> Name -> Directive
       RewriteName : Name -> Name -> Directive
       PrimInteger : Name -> Directive
       PrimString : Name -> Directive
       PrimChar : Name -> Directive
       PrimDouble : Name -> Directive
       CGAction : String -> String -> Directive
       Names : Name -> List String -> Directive
       StartExpr : PTerm' nm -> Directive
       Overloadable : Name -> Directive
       Extension : LangExt -> Directive
       DefaultTotality : TotalReq -> Directive
       PrefixRecordProjections : Bool -> Directive
       AutoImplicitDepth : Nat -> Directive
       NFMetavarThreshold : Nat -> Directive
       SearchTimeout : Integer -> Directive

  directiveList : List Directive
  directiveList =
      [ (Hide ph), (Logging Nothing), (LazyOn False)
      , (UnboundImplicits False), (AmbigDepth 0)
      , (PairNames ph ph ph), (RewriteName ph ph)
      , (PrimInteger ph), (PrimString ph), (PrimChar ph)
      , (PrimDouble ph), (CGAction "" ""), (Names ph [])
      , (StartExpr (PRef EmptyFC ph)), (Overloadable ph)
      , (Extension ElabReflection), (DefaultTotality PartialOK)
      , (PrefixRecordProjections True), (AutoImplicitDepth 0)
      , (NFMetavarThreshold 0), (SearchTimeout 0)
      ]

      where
        -- placeholder
        ph : Name
        ph = UN $ Basic ""

  isPragma : Directive -> Bool
  isPragma (CGAction _ _) = False
  isPragma _              = True

  export
  pragmaTopics : String
  pragmaTopics =
    show $ vsep $ map (((<++>) "+") . pretty {ann=()} . showDirective) $ filter isPragma directiveList
    where
      showDirective : Directive -> String
      showDirective (Hide _)             = "%hide name"
      showDirective (Logging _)          = "%logging [topic] lvl"
      showDirective (LazyOn _)           = "%auto_lazy on|off"
      showDirective (UnboundImplicits _) = "%unbound_implicits"
      showDirective (AmbigDepth _)       = "%ambiguity_depth n"
      showDirective (PairNames _ _ _)    = "%pair ty f s"
      showDirective (RewriteName _ _)    = "%rewrite eq rw"
      showDirective (PrimInteger _)      = "%integerLit n"
      showDirective (PrimString _)       = "%stringLit n"
      showDirective (PrimChar _)         = "%charLit n"
      showDirective (PrimDouble _)       = "%doubleLit n"
      showDirective (CGAction _ _)       = "--directive d"
      showDirective (Names _ _)          = "%name ty ns"
      showDirective (StartExpr _)        = "%start expr"
      showDirective (Overloadable _)     = "%allow_overloads"
      showDirective (Extension _)        = "%language"
      showDirective (DefaultTotality _)  =
        "%default partial|total|covering"
      showDirective (PrefixRecordProjections _) =
        "%prefix_record_projections on|off"
      showDirective (AutoImplicitDepth _) =
        "%auto_implicit_depth n"
      showDirective (NFMetavarThreshold _) =
        "%nf_metavar_threshold n"
      showDirective (SearchTimeout _) =
        "%search_timeout ms"

  public export
  PField : Type
  PField = PField' Name

  public export
  data PField' : Type -> Type where
       MkField : FC -> (doc : String) -> RigCount -> PiInfo (PTerm' nm) ->
                 Name -> (ty : PTerm' nm) -> PField' nm

  -- For noting the pass we're in when desugaring a mutual block
  -- TODO: Decide whether we want mutual blocks!
  public export
  data Pass = Single | AsType | AsDef

  export
  Eq Pass where
    Single == Single = True
    AsType == AsType = True
    AsDef == AsDef = True
    _ == _ = False

  export
  typePass : Pass -> Bool
  typePass p = p == Single || p == AsType

  export
  defPass : Pass -> Bool
  defPass p = p == Single || p == AsDef

  public export
  PFnOpt : Type
  PFnOpt = PFnOpt' Name

  public export
  data PFnOpt' : Type -> Type where
       IFnOpt : FnOpt' nm -> PFnOpt' nm
       PForeign : List (PTerm' nm) -> PFnOpt' nm

  public export
  PDecl : Type
  PDecl = PDecl' Name

  public export
  data PDecl' : Type -> Type where
       PClaim : FC -> RigCount -> Visibility -> List (PFnOpt' nm) -> PTypeDecl' nm -> PDecl' nm
       PDef : FC -> List (PClause' nm) -> PDecl' nm
       PData : FC -> (doc : String) -> Visibility -> PDataDecl' nm -> PDecl' nm
       PParameters : FC ->
                     List (Name, RigCount, PiInfo (PTerm' nm), PTerm' nm) ->
                     List (PDecl' nm) -> PDecl' nm
       PUsing : FC -> List (Maybe Name, PTerm' nm) ->
                List (PDecl' nm) -> PDecl' nm
       PReflect : FC -> PTerm' nm -> PDecl' nm
       PInterface : FC ->
                    Visibility ->
                    (constraints : List (Maybe Name, PTerm' nm)) ->
                    Name ->
                    (doc : String) ->
                    (params : List (Name, (RigCount, PTerm' nm))) ->
                    (det : List Name) ->
                    (conName : Maybe Name) ->
                    List (PDecl' nm) ->
                    PDecl' nm
       PImplementation : FC ->
                         Visibility -> List PFnOpt -> Pass ->
                         (implicits : List (Name, RigCount, PTerm' nm)) ->
                         (constraints : List (Maybe Name, PTerm' nm)) ->
                         Name ->
                         (params : List (PTerm' nm)) ->
                         (implName : Maybe Name) ->
                         (nusing : List Name) ->
                         Maybe (List (PDecl' nm)) ->
                         PDecl' nm
       PRecord : FC ->
                 (doc : String) ->
                 Visibility -> Maybe TotalReq ->
                 Name ->
                 (params : List (Name, RigCount, PiInfo (PTerm' nm), PTerm' nm)) ->
                 (conName : Maybe Name) ->
                 List (PField' nm) ->
                 PDecl' nm

       -- TODO: PPostulate
       -- TODO: POpen (for opening named interfaces)
       PMutual : FC -> List (PDecl' nm) -> PDecl' nm
       PFixity : FC -> Fixity -> Nat -> OpStr -> PDecl' nm
       PNamespace : FC -> Namespace -> List (PDecl' nm) -> PDecl' nm
       PTransform : FC -> String -> PTerm' nm -> PTerm' nm -> PDecl' nm
       PRunElabDecl : FC -> PTerm' nm -> PDecl' nm
       PDirective : FC -> Directive -> PDecl' nm
       PBuiltin : FC -> BuiltinType -> Name -> PDecl' nm

  export
  getPDeclLoc : PDecl' nm -> FC
  getPDeclLoc (PClaim fc _ _ _ _) = fc
  getPDeclLoc (PDef fc _) = fc
  getPDeclLoc (PData fc _ _ _) = fc
  getPDeclLoc (PParameters fc _ _) = fc
  getPDeclLoc (PUsing fc _ _) = fc
  getPDeclLoc (PReflect fc _) = fc
  getPDeclLoc (PInterface fc _ _ _ _ _ _ _ _) = fc
  getPDeclLoc (PImplementation fc _ _ _ _ _ _ _ _ _ _) = fc
  getPDeclLoc (PRecord fc _ _ _ _ _ _ _) = fc
  getPDeclLoc (PMutual fc _) = fc
  getPDeclLoc (PFixity fc _ _ _) = fc
  getPDeclLoc (PNamespace fc _ _) = fc
  getPDeclLoc (PTransform fc _ _ _) = fc
  getPDeclLoc (PRunElabDecl fc _) = fc
  getPDeclLoc (PDirective fc _) = fc
  getPDeclLoc (PBuiltin fc _ _) = fc

export
isStrInterp : PStr -> Maybe FC
isStrInterp (StrInterp fc _) = Just fc
isStrInterp (StrLiteral _ _) = Nothing

export
isStrLiteral : PStr -> Maybe (FC, String)
isStrLiteral (StrInterp _ _) = Nothing
isStrLiteral (StrLiteral fc str) = Just (fc, str)

export
isPDef : PDecl -> Maybe (FC, List PClause)
isPDef (PDef annot cs) = Just (annot, cs)
isPDef _ = Nothing


definedInData : PDataDecl -> List Name
definedInData (MkPData _ n _ _ cons) = n :: map getName cons
  where
    getName : PTypeDecl -> Name
    getName (MkPTy _ _ n _ _) = n
definedInData (MkPLater _ n _) = [n]

export
definedIn : List PDecl -> List Name
definedIn [] = []
definedIn (PClaim _ _ _ _ (MkPTy _ _ n _ _) :: ds) = n :: definedIn ds
definedIn (PData _ _ _ d :: ds) = definedInData d ++ definedIn ds
definedIn (PParameters _ _ pds :: ds) = definedIn pds ++ definedIn ds
definedIn (PUsing _ _ pds :: ds) = definedIn pds ++ definedIn ds
definedIn (PNamespace _ _ ns :: ds) = definedIn ns ++ definedIn ds
definedIn (_ :: ds) = definedIn ds

public export
data REPLEval : Type where
     EvalTC : REPLEval -- Evaluate as if part of the typechecker
     NormaliseAll : REPLEval -- Normalise everything (default)
     Execute : REPLEval -- Evaluate then pass to an executer
     Scheme : REPLEval -- Use the scheme evaluator

export
Show REPLEval where
  show EvalTC = "typecheck"
  show NormaliseAll = "normalise"
  show Execute = "execute"
  show Scheme = "scheme"

export
Pretty REPLEval where
  pretty EvalTC = pretty "typecheck"
  pretty NormaliseAll = pretty "normalise"
  pretty Execute = pretty "execute"
  pretty Scheme = pretty "scheme"

public export
data REPLOpt : Type where
     ShowImplicits : Bool -> REPLOpt
     ShowNamespace : Bool -> REPLOpt
     ShowTypes : Bool -> REPLOpt
     EvalMode : REPLEval -> REPLOpt
     Editor : String -> REPLOpt
     CG : String -> REPLOpt
     Profile : Bool -> REPLOpt
     EvalTiming : Bool -> REPLOpt

export
Show REPLOpt where
  show (ShowImplicits impl) = "showimplicits = " ++ show impl
  show (ShowNamespace ns) = "shownamespace = " ++ show ns
  show (ShowTypes typs) = "showtypes = " ++ show typs
  show (EvalMode mod) = "eval = " ++ show mod
  show (Editor editor) = "editor = " ++ show editor
  show (CG str) = "cg = " ++ str
  show (Profile p) = "profile = " ++ show p
  show (EvalTiming p) = "evaltiming = " ++ show p

export
Pretty REPLOpt where
  pretty (ShowImplicits impl) = pretty "showimplicits" <++> equals <++> pretty impl
  pretty (ShowNamespace ns) = pretty "shownamespace" <++> equals <++> pretty ns
  pretty (ShowTypes typs) = pretty "showtypes" <++> equals <++> pretty typs
  pretty (EvalMode mod) = pretty "eval" <++> equals <++> pretty mod
  pretty (Editor editor) = pretty "editor" <++> equals <++> pretty editor
  pretty (CG str) = pretty "cg" <++> equals <++> pretty str
  pretty (Profile p) = pretty "profile" <++> equals <++> pretty p
  pretty (EvalTiming p) = pretty "evaltiming" <++> equals <++> pretty p

public export
data EditCmd : Type where
     TypeAt : Int -> Int -> Name -> EditCmd
     CaseSplit : Bool -> Int -> Int -> Name -> EditCmd
     AddClause : Bool -> Int -> Name -> EditCmd
     ExprSearch : Bool -> Int -> Name -> List Name -> EditCmd
     ExprSearchNext : EditCmd
     GenerateDef : Bool -> Int -> Name -> Nat -> EditCmd
     GenerateDefNext : EditCmd
     MakeLemma : Bool -> Int -> Name -> EditCmd
     MakeCase : Bool -> Int -> Name -> EditCmd
     MakeWith : Bool -> Int -> Name -> EditCmd

public export
data DocDirective : Type where
  ||| A reserved keyword
  Keyword : String -> DocDirective
  ||| A reserved symbol
  Symbol  : String -> DocDirective
  ||| An arbitrary PTerm
  APTerm  : PTerm -> DocDirective

public export
data REPLCmd : Type where
     NewDefn : List PDecl -> REPLCmd
     Eval : PTerm -> REPLCmd
     Check : PTerm -> REPLCmd
     CheckWithImplicits : PTerm -> REPLCmd
     PrintDef : Name -> REPLCmd
     Reload : REPLCmd
     Load : String -> REPLCmd
     ImportMod : ModuleIdent -> REPLCmd
     Edit : REPLCmd
     Compile : PTerm -> String -> REPLCmd
     Exec : PTerm -> REPLCmd
     Help : REPLCmd
     TypeSearch : PTerm -> REPLCmd
     FuzzyTypeSearch : PTerm -> REPLCmd
     DebugInfo : Name -> REPLCmd
     SetOpt : REPLOpt -> REPLCmd
     GetOpts : REPLCmd
     CGDirective : String -> REPLCmd
     CD : String -> REPLCmd
     CWD: REPLCmd
     Missing : Name -> REPLCmd
     Total : Name -> REPLCmd
     Doc : DocDirective -> REPLCmd
     Browse : Namespace -> REPLCmd
     SetLog : Maybe LogLevel -> REPLCmd
     SetConsoleWidth : Maybe Nat -> REPLCmd
     SetColor : Bool -> REPLCmd
     Metavars : REPLCmd
     Editing : EditCmd -> REPLCmd
     RunShellCommand : String -> REPLCmd
     ShowVersion : REPLCmd
     Quit : REPLCmd
     NOP : REPLCmd
     ImportPackage : String -> REPLCmd

public export
record Import where
  constructor MkImport
  loc : FC
  reexport : Bool
  path : ModuleIdent
  nameAs : Namespace

public export
record Module where
  constructor MkModule
  headerLoc : FC
  moduleNS : ModuleIdent
  imports : List Import
  documentation : String
  decls : List PDecl

parameters {0 nm : Type} (toName : nm -> Name)

  showAlt : PClause' nm -> String
  showDo : PDo' nm -> String
  showPStr : PStr' nm -> String
  showUpdate : PFieldUpdate' nm -> String
  showPTermPrec : Prec -> PTerm' nm -> String
  showOpPrec : Prec -> OpStr' nm -> String

  showPTerm : PTerm' nm -> String
  showPTerm = showPTermPrec Open

  showAlt (MkPatClause _ lhs rhs _) =
    " | " ++ showPTerm lhs ++ " => " ++ showPTerm rhs ++ ";"
  showAlt (MkWithClause _ lhs wval prf flags cs) = " | <<with alts not possible>>;"
  showAlt (MkImpossible _ lhs) = " | " ++ showPTerm lhs ++ " impossible;"

  showDo (DoExp _ tm) = showPTerm tm
  showDo (DoBind _ _ n tm) = show n ++ " <- " ++ showPTerm tm
  showDo (DoBindPat _ l tm alts)
      = showPTerm l ++ " <- " ++ showPTerm tm ++ concatMap showAlt alts
  showDo (DoLet _ _ l rig _ tm) = "let " ++ show l ++ " = " ++ showPTerm tm
  showDo (DoLetPat _ l _ tm alts)
      = "let " ++ showPTerm l ++ " = " ++ showPTerm tm ++ concatMap showAlt alts
  showDo (DoLetLocal _ ds)
      -- We'll never see this when displaying a normal form...
      = "let { << definitions >>  }"
  showDo (DoRewrite _ rule)
      = "rewrite " ++ showPTerm rule

  showPStr (StrLiteral _ str) = show str
  showPStr (StrInterp _ tm) = showPTerm tm

  showUpdate (PSetField p v) = showSep "." p ++ " = " ++ showPTerm v
  showUpdate (PSetFieldApp p v) = showSep "." p ++ " $= " ++ showPTerm v

  showPTermPrec d (PRef _ n) = showPrec d (toName n)
  showPTermPrec d (PPi _ rig Explicit Nothing arg ret)
        = showPTermPrec d arg ++ " -> " ++ showPTermPrec d ret
  showPTermPrec d (PPi _ rig Explicit (Just n) arg ret)
        = "(" ++ showCount rig ++ showPrec d n
         ++ " : " ++ showPTermPrec d arg ++ ") -> "
         ++ showPTermPrec d ret
  showPTermPrec d (PPi _ rig Implicit Nothing arg ret) -- shouldn't happen
        = "{" ++ showCount rig ++ "_ : " ++ showPTermPrec d arg ++ "} -> "
          ++ showPTermPrec d ret
  showPTermPrec d (PPi _ rig Implicit (Just n) arg ret)
        = "{" ++ showCount rig ++ showPrec d n ++ " : " ++ showPTermPrec d arg ++ "} -> " ++ showPTermPrec d ret
  showPTermPrec d (PPi _ top AutoImplicit Nothing arg ret)
        = showPTermPrec d arg ++ " => " ++ showPTermPrec d ret
  showPTermPrec d (PPi _ rig AutoImplicit (Just n) arg ret)
        = "{auto " ++ showCount rig ++ showPrec d n ++ " : " ++ showPTermPrec d arg ++ "} -> " ++ showPTermPrec d ret
  showPTermPrec d (PPi _ rig (DefImplicit t) Nothing arg ret) -- shouldn't happen
        = "{default " ++ showPTermPrec App t ++ " " ++ showCount rig ++ "_ : " ++ showPTermPrec d arg ++ "} -> " ++ showPTermPrec d ret
  showPTermPrec d (PPi _ rig (DefImplicit t) (Just n) arg ret)
        = "{default " ++ showPTermPrec App t ++ " " ++ showCount rig ++ showPrec d n ++ " : " ++ showPTermPrec d arg ++ "} -> " ++ showPTermPrec d ret
  showPTermPrec d (PLam _ rig _ n (PImplicit _) sc)
        = "\\" ++ showCount rig ++ showPTermPrec d n ++ " => " ++ showPTermPrec d sc
  showPTermPrec d (PLam _ rig _ n ty sc)
        = "\\" ++ showCount rig ++ showPTermPrec d n ++ " : " ++ showPTermPrec d ty ++ " => " ++ showPTermPrec d sc
  showPTermPrec d (PLet _ rig n (PImplicit _) val sc alts)
        = "let " ++ showCount rig ++ showPTermPrec d n ++ " = " ++ showPTermPrec d val ++ " in " ++ showPTermPrec d sc
  showPTermPrec d (PLet _ rig n ty val sc alts)
        = "let " ++ showCount rig ++ showPTermPrec d n ++ " : " ++ showPTermPrec d ty ++ " = "
                 ++ showPTermPrec d val ++ concatMap showAlt alts ++
                 " in " ++ showPTermPrec d sc
  showPTermPrec _ (PCase _ tm cs)
        = "case " ++ showPTerm tm ++ " of { " ++
            showSep " ; " (map showCase cs) ++ " }"
      where
        showCase : PClause' nm -> String
        showCase (MkPatClause _ lhs rhs _) = showPTerm lhs ++ " => " ++ showPTerm rhs
        showCase (MkWithClause _ lhs rhs _ flags _) = " | <<with alts not possible>>"
        showCase (MkImpossible _ lhs) = showPTerm lhs ++ " impossible"
  showPTermPrec d (PLocal _ ds sc) -- We'll never see this when displaying a normal form...
        = "let { << definitions >>  } in " ++ showPTermPrec d sc
  showPTermPrec d (PUpdate _ fs)
        = "record { " ++ showSep ", " (map showUpdate fs) ++ " }"
  showPTermPrec d (PApp _ f a) =
      let catchall : Lazy String := showPTermPrec App f ++ " " ++ showPTermPrec App a in
      case f of
        PRef _ n =>
          if isJust (isRF (toName n))
          then showPTermPrec App a ++ " " ++ showPTermPrec App f
          else catchall
        _ => catchall
  showPTermPrec d (PWithApp _ f a) = showPTermPrec d f ++ " | " ++ showPTermPrec d a
  showPTermPrec d (PAutoApp _ f a)
        = showPTermPrec d f ++ " @{" ++ showPTermPrec d a ++ "}"
  showPTermPrec d (PDelayed _ LInf ty)
        = showParens (d >= App) $ "Inf " ++ showPTermPrec App ty
  showPTermPrec d (PDelayed _ _ ty)
        = showParens (d >= App) $ "Lazy " ++ showPTermPrec App ty
  showPTermPrec d (PDelay _ tm)
        = showParens (d >= App) $ "Delay " ++ showPTermPrec App tm
  showPTermPrec d (PForce _ tm)
        = showParens (d >= App) $ "Force " ++ showPTermPrec App tm
  showPTermPrec d (PNamedApp _ f n (PRef _ a))
        = if n == (toName a)
             then showPTermPrec d f ++ " {" ++ showPrec d n ++ "}"
             else showPTermPrec d f ++ " {" ++ showPrec d n ++ " = " ++ showPrec d (toName a) ++ "}"
  showPTermPrec d (PNamedApp _ f n a)
        = showPTermPrec d f ++ " {" ++ showPrec d n ++ " = " ++ showPTermPrec d a ++ "}"
  showPTermPrec _ (PSearch _ _) = "%search"
  showPTermPrec d (PQuote _ tm) = "`(" ++ showPTermPrec d tm ++ ")"
  showPTermPrec d (PQuoteName _ n) = "`{" ++ showPrec d n ++ "}"
  showPTermPrec d (PQuoteDecl _ tm) = "`[ <<declaration>> ]"
  showPTermPrec d (PUnquote _ tm) = "~(" ++ showPTermPrec d tm ++ ")"
  showPTermPrec d (PRunElab _ tm) = "%runElab " ++ showPTermPrec d tm
  showPTermPrec d (PPrimVal _ c) = showPrec d c
  showPTermPrec _ (PHole _ _ n) = "?" ++ n
  showPTermPrec _ (PType _) = "Type"
  showPTermPrec d (PAs _ _ n p) = showPrec d n ++ "@" ++ showPTermPrec d p
  showPTermPrec d (PDotted _ p) = "." ++ showPTermPrec d p
  showPTermPrec _ (PImplicit _) = "_"
  showPTermPrec _ (PInfer _) = "?"
  showPTermPrec d (POp _ _ op x y) = showPTermPrec d x ++ " " ++ showOpPrec d op ++ " " ++ showPTermPrec d y
  showPTermPrec d (PPrefixOp _ _ op x) = showOpPrec d op ++ showPTermPrec d x
  showPTermPrec d (PSectionL _ _ op x) = "(" ++ showOpPrec d op ++ " " ++ showPTermPrec d x ++ ")"
  showPTermPrec d (PSectionR _ _ x op) = "(" ++ showPTermPrec d x ++ " " ++ showOpPrec d op ++ ")"
  showPTermPrec d (PEq fc l r) = showPTermPrec d l ++ " = " ++ showPTermPrec d r
  showPTermPrec d (PBracketed _ tm) = "(" ++ showPTermPrec d tm ++ ")"
  showPTermPrec d (PString _ xs) = join " ++ " $ showPStr <$> xs
  showPTermPrec d (PMultiline _ indent xs) = "multiline (" ++ (join " ++ " $ showPStr <$> concat xs) ++ ")"
  showPTermPrec d (PDoBlock _ ns ds)
        = "do " ++ showSep " ; " (map showDo ds)
  showPTermPrec d (PBang _ tm) = "!" ++ showPTermPrec d tm
  showPTermPrec d (PIdiom _ tm) = "[|" ++ showPTermPrec d tm ++ "|]"
  showPTermPrec d (PList _ _ xs)
        = "[" ++ showSep ", " (map (showPTermPrec d . snd) xs) ++ "]"
  showPTermPrec d (PSnocList _ _ xs)
        = "[<" ++ showSep ", " (map (showPTermPrec d . snd) (xs <>> [])) ++ "]"
  showPTermPrec d (PPair _ l r) = "(" ++ showPTermPrec d l ++ ", " ++ showPTermPrec d r ++ ")"
  showPTermPrec d (PDPair _ _ l (PImplicit _) r) = "(" ++ showPTermPrec d l ++ " ** " ++ showPTermPrec d r ++ ")"
  showPTermPrec d (PDPair _ _ l ty r) = "(" ++ showPTermPrec d l ++ " : " ++ showPTermPrec d ty ++
                                 " ** " ++ showPTermPrec d r ++ ")"
  showPTermPrec _ (PUnit _) = "()"
  showPTermPrec d (PIfThenElse _ x t e) = "if " ++ showPTermPrec d x ++ " then " ++ showPTermPrec d t ++
                                 " else " ++ showPTermPrec d e
  showPTermPrec d (PComprehension _ ret es)
        = "[" ++ showPTermPrec d (dePure ret) ++ " | " ++
                 showSep ", " (map (showDo . deGuard) es) ++ "]"
      where
        dePure : PTerm' nm -> PTerm' nm
        dePure tm@(PApp _ (PRef _ n) arg)
            = if dropNS (toName n) == UN (Basic "pure") then arg else tm
        dePure tm = tm

        deGuard : PDo' nm -> PDo' nm
        deGuard tm@(DoExp fc (PApp _ (PRef _ n) arg))
            = if dropNS (toName n) == UN (Basic "guard") then DoExp fc arg else tm
        deGuard tm = tm
  showPTermPrec d (PRewrite _ rule tm)
        = "rewrite " ++ showPTermPrec d rule ++ " in " ++ showPTermPrec d tm
  showPTermPrec d (PRange _ start Nothing end)
        = "[" ++ showPTermPrec d start ++ " .. " ++ showPTermPrec d end ++ "]"
  showPTermPrec d (PRange _ start (Just next) end)
        = "[" ++ showPTermPrec d start ++ ", " ++ showPTermPrec d next ++ " .. " ++ showPTermPrec d end ++ "]"
  showPTermPrec d (PRangeStream _ start Nothing)
        = "[" ++ showPTermPrec d start ++ " .. ]"
  showPTermPrec d (PRangeStream _ start (Just next))
        = "[" ++ showPTermPrec d start ++ ", " ++ showPTermPrec d next ++ " .. ]"
  showPTermPrec d (PUnifyLog _ _ tm) = showPTermPrec d tm
  showPTermPrec d (PPostfixApp fc rec fields)
        = showPTermPrec d rec ++ concatMap (\n => "." ++ show n) fields
  showPTermPrec d (PPostfixAppPartial fc fields)
        = concatMap (\n => "." ++ show n) fields
  showPTermPrec d (PWithUnambigNames fc ns rhs)
        = "with " ++ show ns ++ " " ++ showPTermPrec d rhs

  showOpPrec d op = let op = toName op in
    if isOpName op
    then        showPrec d op
    else "`" ++ showPrec d op ++ "`"

export
covering
Show PTerm where
  showPrec = showPTermPrec id

export
covering
Show IPTerm where
  showPrec = showPTermPrec rawName

public export
record Method where
  constructor MkMethod
  name     : Name
  count    : RigCount
  totalReq : Maybe TotalReq
  type     : RawImp

export
covering
Show Method where
  show (MkMethod n c treq ty)
    = "[" ++ show treq ++ "] " ++ show c ++ " " ++ show n ++ " : " ++ show ty

public export
record IFaceInfo where
  constructor MkIFaceInfo
  iconstructor : Name
  implParams : List Name
  params : List Name
  parents : List RawImp
  methods : List Method
     -- ^ name, whether a data method, and desugared type (without constraint)
  defaults : List (Name, List ImpClause)

export
TTC Method where
  toBuf b (MkMethod nm c treq ty)
      = do toBuf b nm
           toBuf b c
           toBuf b treq
           toBuf b ty

  fromBuf b
      = do nm <- fromBuf b
           c <- fromBuf b
           treq <- fromBuf b
           ty <- fromBuf b
           pure (MkMethod nm c treq ty)


export
TTC IFaceInfo where
  toBuf b (MkIFaceInfo ic impps ps cs ms ds)
      = do toBuf b ic
           toBuf b impps
           toBuf b ps
           toBuf b cs
           toBuf b ms
           toBuf b ds

  fromBuf b
      = do ic <- fromBuf b
           impps <- fromBuf b
           ps <- fromBuf b
           cs <- fromBuf b
           ms <- fromBuf b
           ds <- fromBuf b
           pure (MkIFaceInfo ic impps ps cs ms ds)

-- If you update this, update 'extendSyn' in Desugar to keep it up to date
-- when reading imports
public export
record SyntaxInfo where
  constructor MkSyntax
  -- Keep infix/prefix, then we can define operators which are both
  -- (most obviously, -)
  infixes : StringMap (Fixity, Nat)
  prefixes : StringMap Nat
  -- info about modules
  saveMod : List ModuleIdent -- current module name
  modDocstrings : SortedMap ModuleIdent String
  -- info about interfaces
  saveIFaces : List Name -- interfaces defined in current session, to save
                         -- to ttc
  ifaces : ANameMap IFaceInfo
  -- info about definitions
  saveDocstrings : NameMap () -- names defined in current session
  defDocstrings : ANameMap String
  bracketholes : List Name -- hole names in argument position (so need
                           -- to be bracketed when solved)
  usingImpl : List (Maybe Name, RawImp)
  startExpr : RawImp
  holeNames : List String -- hole names in the file

export
TTC Fixity where
  toBuf b InfixL = tag 0
  toBuf b InfixR = tag 1
  toBuf b Infix = tag 2
  toBuf b Prefix = tag 3

  fromBuf b
      = case !getTag of
             0 => pure InfixL
             1 => pure InfixR
             2 => pure Infix
             3 => pure Prefix
             _ => corrupt "Fixity"

export
TTC SyntaxInfo where
  toBuf b syn
      = do toBuf b (StringMap.toList (infixes syn))
           toBuf b (StringMap.toList (prefixes syn))
           toBuf b (filter (\n => elemBy (==) (fst n) (saveMod syn))
                           (SortedMap.toList $ modDocstrings syn))
           toBuf b (filter (\n => fst n `elem` saveIFaces syn)
                           (ANameMap.toList (ifaces syn)))
           toBuf b (filter (\n => isJust (lookup (fst n) (saveDocstrings syn)))
                           (ANameMap.toList (defDocstrings syn)))
           toBuf b (bracketholes syn)
           toBuf b (startExpr syn)
           toBuf b (holeNames syn)

  fromBuf b
      = do inf <- fromBuf b
           pre <- fromBuf b
           moddstr <- fromBuf b
           ifs <- fromBuf b
           defdstrs <- fromBuf b
           bhs <- fromBuf b
           start <- fromBuf b
           hnames <- fromBuf b
           pure $ MkSyntax (fromList inf) (fromList pre)
                   [] (fromList moddstr)
                   [] (fromList ifs)
                   empty (fromList defdstrs)
                   bhs
                   [] start
                   hnames

HasNames IFaceInfo where
  full gam iface
      = do -- coreLift $ printLn (iconstructor iface)
           -- coreLift $ printLn (methods iface)
           pure iface

  resolved gam iface = pure iface

HasNames a => HasNames (ANameMap a) where
  full gam nmap
      = insertAll empty (toList nmap)
    where
      insertAll : ANameMap a -> List (Name, a) -> Core (ANameMap a)
      insertAll ms [] = pure ms
      insertAll ms ((k, v) :: ns)
          = insertAll (addName !(full gam k) !(full gam v) ms) ns

  resolved gam nmap
      = insertAll empty (toList nmap)
    where
      insertAll : ANameMap a -> List (Name, a) -> Core (ANameMap a)
      insertAll ms [] = pure ms
      insertAll ms ((k, v) :: ns)
          = insertAll (addName !(resolved gam k) !(resolved gam v) ms) ns

export
HasNames SyntaxInfo where
  full gam syn
      = pure $ { ifaces := !(full gam (ifaces syn))
               , bracketholes := !(traverse (full gam) (bracketholes syn))
               } syn
  resolved gam syn
      = pure $ { ifaces := !(resolved gam (ifaces syn))
               , bracketholes := !(traverse (resolved gam) (bracketholes syn))
               } syn

export
initSyntax : SyntaxInfo
initSyntax
    = MkSyntax initInfix
               initPrefix
               []
               empty
               []
               empty
               initSaveDocStrings
               initDocStrings
               []
               []
               (IVar EmptyFC (UN $ Basic "main"))
               []

  where

    initInfix : StringMap (Fixity, Nat)
    initInfix = insert "=" (Infix, 0) empty

    initPrefix : StringMap Nat
    initPrefix = fromList
      [ ("-", 10)
      , ("negate", 10) -- for documentation purposes
      ]

    initDocStrings : ANameMap String
    initDocStrings = empty

    initSaveDocStrings : NameMap ()
    initSaveDocStrings = empty

-- A label for Syntax info in the global state
export
data Syn : Type where

export
withSyn : {auto s : Ref Syn SyntaxInfo} -> Core a -> Core a
withSyn = wrapRef Syn (\_ => pure ())

export
mapPTermM : (PTerm' nm -> Core (PTerm' nm)) -> PTerm' nm -> Core (PTerm' nm)
mapPTermM f = goPTerm where

  mutual

    goPTerm : PTerm' nm -> Core (PTerm' nm)
    goPTerm t@(PRef _ _) = f t
    goPTerm (PPi fc x info z argTy retTy) =
      PPi fc x <$> goPiInfo info
               <*> pure z
               <*> goPTerm argTy
               <*> goPTerm retTy
      >>= f
    goPTerm (PLam fc x info z argTy scope) =
      PLam fc x <$> goPiInfo info
                <*> pure z
                <*> goPTerm argTy
                <*> goPTerm scope
      >>= f
    goPTerm (PLet fc x pat nTy nVal scope alts) =
      PLet fc x <$> goPTerm pat
                <*> goPTerm nTy
                <*> goPTerm nVal
                <*> goPTerm scope
                <*> goPClauses alts
      >>= f
    goPTerm (PCase fc x xs) =
      PCase fc <$> goPTerm x
               <*> goPClauses xs
      >>= f
    goPTerm (PLocal fc xs scope) =
      PLocal fc <$> goPDecls xs
                <*> goPTerm scope
      >>= f
    goPTerm (PUpdate fc xs) =
      PUpdate fc <$> goPFieldUpdates xs
      >>= f
    goPTerm (PApp fc x y) =
      PApp fc <$> goPTerm x
              <*> goPTerm y
      >>= f
    goPTerm (PWithApp fc x y) =
      PWithApp fc <$> goPTerm x
                  <*> goPTerm y
      >>= f
    goPTerm (PAutoApp fc x y) =
      PAutoApp fc <$> goPTerm x
                         <*> goPTerm y
      >>= f
    goPTerm (PNamedApp fc x n y) =
      PNamedApp fc <$> goPTerm x
                   <*> pure n
                   <*> goPTerm y
      >>= f
    goPTerm (PDelayed fc x y) =
      PDelayed fc x <$> goPTerm y
      >>= f
    goPTerm (PDelay fc x) =
      PDelay fc <$> goPTerm x
      >>= f
    goPTerm (PForce fc x) =
      PForce fc <$> goPTerm x
      >>= f
    goPTerm t@(PSearch _ _) = f t
    goPTerm t@(PPrimVal _ _) = f t
    goPTerm (PQuote fc x) =
      PQuote fc <$> goPTerm x
      >>= f
    goPTerm t@(PQuoteName _ _) = f t
    goPTerm (PQuoteDecl fc x) =
      PQuoteDecl fc <$> traverse goPDecl x
      >>= f
    goPTerm (PUnquote fc x) =
      PUnquote fc <$> goPTerm x
      >>= f
    goPTerm (PRunElab fc x) =
      PRunElab fc <$> goPTerm x
      >>= f
    goPTerm t@(PHole _ _ _) = f t
    goPTerm t@(PType _) = f t
    goPTerm (PAs fc nameFC x pat) =
      PAs fc nameFC x <$> goPTerm pat
      >>= f
    goPTerm (PDotted fc x) =
      PDotted fc <$> goPTerm x
      >>= f
    goPTerm t@(PImplicit _) = f t
    goPTerm t@(PInfer _) = f t
    goPTerm (POp fc opFC x y z) =
      POp fc opFC x <$> goPTerm y
                    <*> goPTerm z
      >>= f
    goPTerm (PPrefixOp fc opFC x y) =
      PPrefixOp fc opFC x <$> goPTerm y
      >>= f
    goPTerm (PSectionL fc opFC x y) =
      PSectionL fc opFC x <$> goPTerm y
      >>= f
    goPTerm (PSectionR fc opFC x y) =
      PSectionR fc opFC <$> goPTerm x
                   <*> pure y
      >>= f
    goPTerm (PEq fc x y) =
      PEq fc <$> goPTerm x
             <*> goPTerm y
      >>= f
    goPTerm (PBracketed fc x) =
      PBracketed fc <$> goPTerm x
      >>= f
    goPTerm (PString fc xs) =
      PString fc <$> goPStrings xs
      >>= f
    goPTerm (PMultiline fc x ys) =
      PMultiline fc x <$> goPStringLines ys
      >>= f
    goPTerm (PDoBlock fc ns xs) =
      PDoBlock fc ns <$> goPDos xs
      >>= f
    goPTerm (PBang fc x) =
      PBang fc <$> goPTerm x
      >>= f
    goPTerm (PIdiom fc x) =
      PIdiom fc <$> goPTerm x
      >>= f
    goPTerm (PList fc nilFC xs) =
      PList fc nilFC <$> goPairedPTerms xs
      >>= f
    goPTerm (PSnocList fc nilFC xs) =
      PSnocList fc nilFC <$> goPairedSnocPTerms xs
      >>= f
    goPTerm (PPair fc x y) =
      PPair fc <$> goPTerm x
               <*> goPTerm y
      >>= f
    goPTerm (PDPair fc opFC x y z) =
      PDPair fc opFC
                <$> goPTerm x
                <*> goPTerm y
                <*> goPTerm z
      >>= f
    goPTerm t@(PUnit _) = f t
    goPTerm (PIfThenElse fc x y z) =
      PIfThenElse fc <$> goPTerm x
                     <*> goPTerm y
                     <*> goPTerm z
      >>= f
    goPTerm (PComprehension fc x xs) =
      PComprehension fc <$> goPTerm x
                        <*> goPDos xs
      >>= f
    goPTerm (PRewrite fc x y) =
      PRewrite fc <$> goPTerm x
                  <*> goPTerm y
      >>= f
    goPTerm (PRange fc x y z) =
      PRange fc <$> goPTerm x
                <*> goMPTerm y
                <*> goPTerm z
      >>= f
    goPTerm (PRangeStream fc x y) =
      PRangeStream fc <$> goPTerm x
                      <*> goMPTerm y
      >>= f
    goPTerm (PUnifyLog fc k x) =
      PUnifyLog fc k <$> goPTerm x
      >>= f
    goPTerm (PPostfixApp fc rec fields) =
      PPostfixApp fc <$> goPTerm rec <*> pure fields
      >>= f
    goPTerm (PPostfixAppPartial fc fields) =
      f (PPostfixAppPartial fc fields)
    goPTerm (PWithUnambigNames fc ns rhs) =
      PWithUnambigNames fc ns <$> goPTerm rhs
      >>= f

    goPFieldUpdate : PFieldUpdate' nm -> Core (PFieldUpdate' nm)
    goPFieldUpdate (PSetField p t)    = PSetField p <$> goPTerm t
    goPFieldUpdate (PSetFieldApp p t) = PSetFieldApp p <$> goPTerm t

    goPStr : PStr' nm -> Core (PStr' nm)
    goPStr (StrInterp fc t) = StrInterp fc <$> goPTerm t
    goPStr x                = pure x

    goPDo : PDo' nm -> Core (PDo' nm)
    goPDo (DoExp fc t) = DoExp fc <$> goPTerm t
    goPDo (DoBind fc nameFC n t) = DoBind fc nameFC n <$> goPTerm t
    goPDo (DoBindPat fc t u cls) =
      DoBindPat fc <$> goPTerm t
                   <*> goPTerm u
                   <*> goPClauses cls
    goPDo (DoLet fc lhsFC n c t scope) =
       DoLet fc lhsFC n c <$> goPTerm t
                          <*> goPTerm scope
    goPDo (DoLetPat fc pat t scope cls) =
       DoLetPat fc <$> goPTerm pat
                   <*> goPTerm t
                   <*> goPTerm scope
                   <*> goPClauses cls
    goPDo (DoLetLocal fc decls) = DoLetLocal fc <$> goPDecls decls
    goPDo (DoRewrite fc t) = DoRewrite fc <$> goPTerm t

    goPClause : PClause' nm -> Core (PClause' nm)
    goPClause (MkPatClause fc lhs rhs wh) =
      MkPatClause fc <$> goPTerm lhs
                     <*> goPTerm rhs
                     <*> goPDecls wh
    goPClause (MkWithClause fc lhs wVal prf flags cls) =
      MkWithClause fc <$> goPTerm lhs
                      <*> goPTerm wVal
                      <*> pure prf
                      <*> pure flags
                      <*> goPClauses cls
    goPClause (MkImpossible fc lhs) = MkImpossible fc <$> goPTerm lhs

    goPDecl : PDecl' nm -> Core (PDecl' nm)
    goPDecl (PClaim fc c v opts tdecl) =
      PClaim fc c v <$> goPFnOpts opts
                    <*> goPTypeDecl tdecl
    goPDecl (PDef fc cls) = PDef fc <$> goPClauses cls
    goPDecl (PData fc doc v d) = PData fc doc v <$> goPDataDecl d
    goPDecl (PParameters fc nts ps) =
      PParameters fc <$> go4TupledPTerms nts
                     <*> goPDecls ps
    goPDecl (PUsing fc mnts ps) =
      PUsing fc <$> goPairedPTerms mnts
                <*> goPDecls ps
    goPDecl (PReflect fc t) = PReflect fc <$> goPTerm t
    goPDecl (PInterface fc v mnts n doc nrts ns mn ps) =
      PInterface fc v <$> goPairedPTerms mnts
                      <*> pure n
                      <*> pure doc
                      <*> go3TupledPTerms nrts
                      <*> pure ns
                      <*> pure mn
                      <*> goPDecls ps
    goPDecl (PImplementation fc v opts p is cs n ts mn ns mps) =
      PImplementation fc v opts p <$> go3TupledPTerms is
                                  <*> goPairedPTerms cs
                                  <*> pure n
                                  <*> goPTerms ts
                                  <*> pure mn
                                  <*> pure ns
                                  <*> goMPDecls mps
    goPDecl (PRecord fc doc v tot n nts mn fs) =
      PRecord fc doc v tot n <$> go4TupledPTerms nts
                             <*> pure mn
                             <*> goPFields fs
    goPDecl (PMutual fc ps) = PMutual fc <$> goPDecls ps
    goPDecl p@(PFixity _ _ _ _) = pure p
    goPDecl (PNamespace fc strs ps) = PNamespace fc strs <$> goPDecls ps
    goPDecl (PTransform fc n a b) = PTransform fc n <$> goPTerm a <*> goPTerm b
    goPDecl (PRunElabDecl fc a) = PRunElabDecl fc <$> goPTerm a
    goPDecl p@(PDirective _ _) = pure p
    goPDecl p@(PBuiltin _ _ _) = pure p


    goPTypeDecl : PTypeDecl' nm -> Core (PTypeDecl' nm)
    goPTypeDecl (MkPTy fc nameFC n d t) = MkPTy fc nameFC n d <$> goPTerm t

    goPDataDecl : PDataDecl' nm -> Core (PDataDecl' nm)
    goPDataDecl (MkPData fc n t opts tdecls) =
      MkPData fc n <$> goPTerm t
                   <*> pure opts
                   <*> goPTypeDecls tdecls
    goPDataDecl (MkPLater fc n t) = MkPLater fc n <$> goPTerm t

    goPField : PField' nm -> Core (PField' nm)
    goPField (MkField fc doc c info n t) =
      MkField fc doc c <$> goPiInfo info
                       <*> pure n
                       <*> goPTerm t

    goPiInfo : PiInfo (PTerm' nm) -> Core (PiInfo (PTerm' nm))
    goPiInfo (DefImplicit t) = DefImplicit <$> goPTerm t
    goPiInfo t = pure t

    goPFnOpt : PFnOpt' nm -> Core (PFnOpt' nm)
    goPFnOpt o@(IFnOpt _) = pure o
    goPFnOpt (PForeign ts) = PForeign <$> goPTerms ts

    -- Traversable stuff. Inlined for termination checking.

    goMPTerm : Maybe (PTerm' nm) -> Core (Maybe $ PTerm' nm)
    goMPTerm Nothing  = pure Nothing
    goMPTerm (Just t) = Just <$> goPTerm t

    goPTerms : List (PTerm' nm) -> Core (List $ PTerm' nm)
    goPTerms []        = pure []
    goPTerms (t :: ts) = (::) <$> goPTerm t <*> goPTerms ts

    goPairedPTerms : List (x, PTerm' nm) -> Core (List (x, PTerm' nm))
    goPairedPTerms []             = pure []
    goPairedPTerms ((a, t) :: ts) =
       (::) . MkPair a <$> goPTerm t
                       <*> goPairedPTerms ts

    goPairedSnocPTerms : SnocList (x, PTerm' nm) -> Core (SnocList (x, PTerm' nm))
    goPairedSnocPTerms [<]            = pure [<]
    goPairedSnocPTerms (ts :< (a, t)) =
       (:<) <$> goPairedSnocPTerms ts
            <*> MkPair a <$> goPTerm t

    go3TupledPTerms : List (x, y, PTerm' nm) -> Core (List (x, y, PTerm' nm))
    go3TupledPTerms [] = pure []
    go3TupledPTerms ((a, b, t) :: ts) =
      (::) . (\ c => (a, b, c)) <$> goPTerm t
                                <*> go3TupledPTerms ts

    go4TupledPTerms : List (x, y, PiInfo (PTerm' nm), PTerm' nm) ->
                      Core (List (x, y, PiInfo (PTerm' nm), PTerm' nm))
    go4TupledPTerms [] = pure []
    go4TupledPTerms ((a, b, p, t) :: ts) =
      (\ p, d, ts => (a, b, p, d) :: ts) <$> goPiInfo p
                                         <*> goPTerm t
                                         <*> go4TupledPTerms ts

    goPStringLines : List (List (PStr' nm)) -> Core (List (List (PStr' nm)))
    goPStringLines []        = pure []
    goPStringLines (line :: lines) = (::) <$> goPStrings line <*> goPStringLines lines

    goPStrings : List (PStr' nm) -> Core (List (PStr' nm))
    goPStrings []        = pure []
    goPStrings (str :: strs) = (::) <$> goPStr str <*> goPStrings strs

    goPDos : List (PDo' nm) -> Core (List (PDo' nm))
    goPDos []        = pure []
    goPDos (d :: ds) = (::) <$> goPDo d <*> goPDos ds

    goPClauses : List (PClause' nm) -> Core (List (PClause' nm))
    goPClauses []          = pure []
    goPClauses (cl :: cls) = (::) <$> goPClause cl <*> goPClauses cls

    goMPDecls : Maybe (List (PDecl' nm)) -> Core (Maybe (List (PDecl' nm)))
    goMPDecls Nothing   = pure Nothing
    goMPDecls (Just ps) = Just <$> goPDecls ps

    goPDecls : List (PDecl' nm) -> Core (List (PDecl' nm))
    goPDecls []          = pure []
    goPDecls (d :: ds) = (::) <$> goPDecl d <*> goPDecls ds

    goPFieldUpdates : List (PFieldUpdate' nm) -> Core (List (PFieldUpdate' nm))
    goPFieldUpdates []          = pure []
    goPFieldUpdates (fu :: fus) = (::) <$> goPFieldUpdate fu <*> goPFieldUpdates fus

    goPFields : List (PField' nm) -> Core (List (PField' nm))
    goPFields []        = pure []
    goPFields (f :: fs) = (::) <$> goPField f <*> goPFields fs

    goPFnOpts : List (PFnOpt' nm) -> Core (List (PFnOpt' nm))
    goPFnOpts []        = pure []
    goPFnOpts (o :: os) = (::) <$> goPFnOpt o <*> goPFnOpts os

    goPTypeDecls : List (PTypeDecl' nm) -> Core (List (PTypeDecl' nm))
    goPTypeDecls []        = pure []
    goPTypeDecls (t :: ts) = (::) <$> goPTypeDecl t <*> goPTypeDecls ts
