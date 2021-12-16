module Idris.Doc.String

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.TT
import Core.TT.Traversals

import Idris.Pretty
import Idris.REPL.Opts
import Idris.Resugar
import Idris.Syntax

import TTImp.TTImp
import TTImp.TTImp.Functor
import TTImp.Elab.Prim

import Data.List
import Data.List1
import Data.Maybe
import Data.String

import Libraries.Data.ANameMap
import Libraries.Data.NameMap
import Libraries.Data.SortedSet
import Libraries.Data.SortedMap
import Libraries.Data.StringMap as S
import Libraries.Data.String.Extra

import public Libraries.Text.PrettyPrint.Prettyprinter
import public Libraries.Text.PrettyPrint.Prettyprinter.Util

import Parser.Lexer.Source

import public Idris.Doc.Annotations
import Idris.Doc.Keywords


%default covering

-- Add a doc string for a module name
export
addModDocString : {auto s : Ref Syn SyntaxInfo} ->
                  ModuleIdent -> String ->
                  Core ()
addModDocString mi doc
    = do syn <- get Syn
         put Syn ({ saveMod $= (mi ::)
                  , modDocstrings $= insert mi doc } syn)

-- Add a doc string for a name in the current namespace
export
addDocString : {auto c : Ref Ctxt Defs} ->
               {auto s : Ref Syn SyntaxInfo} ->
               Name -> String ->
               Core ()
addDocString n_in doc
    = do n <- inCurrentNS n_in
         log "doc.record" 50 $
           "Adding doc for " ++ show n_in ++ " (aka " ++ show n ++ " in current NS)"
         syn <- get Syn
         put Syn ({ defDocstrings $= addName n doc,
                    saveDocstrings $= insert n () } syn)

-- Add a doc string for a name, in an extended namespace (e.g. for
-- record getters)
export
addDocStringNS : {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 Namespace -> Name -> String ->
                 Core ()
addDocStringNS ns n_in doc
    = do n <- inCurrentNS n_in
         let n' = case n of
                       NS old root => NS (old <.> ns) root
                       root => NS ns root
         syn <- get Syn
         put Syn ({ defDocstrings $= addName n' doc,
                    saveDocstrings $= insert n' () } syn)

prettyTerm : IPTerm -> Doc IdrisDocAnn
prettyTerm = reAnnotate Syntax . Idris.Pretty.prettyTerm

prettyName : Name -> Doc IdrisDocAnn
prettyName n =
  case userNameRoot n of
    -- shouldn't happen: we only show UN anyways...
    Nothing => pretty (nameRoot n)
    Just un => if isOpUserName un then parens (pretty un) else pretty un

prettyKindedName : Maybe String -> Doc IdrisDocAnn -> Doc IdrisDocAnn
prettyKindedName Nothing   nm = nm
prettyKindedName (Just kw) nm
  = annotate (Syntax Keyword) (pretty kw) <++> nm

||| Look up implementations
getImplDocs : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              (keep : Term [] -> Core Bool) ->
              Core (List (Doc IdrisDocAnn))
getImplDocs keep
    = do defs <- get Ctxt
         docss <- for (concat $ values $ typeHints defs) $ \ (impl, _) =>
           do Just def <- lookupCtxtExact impl (gamma defs)
                | _ => pure []
              -- Only keep things that look like implementations.
              -- i.e. get rid of data constructors
              let Just Func = defNameType (definition def)
                | _ => pure []
              -- Check that the type mentions the name of interest
              ty <- toFullNames !(normaliseHoles defs [] (type def))
              True <- keep ty
                | False => pure []
              ty <- resugar [] ty
              pure [annotate (Decl impl) $ prettyTerm ty]
         pure $ case concat docss of
           [] => []
           [doc] => [header "Hint" <++> annotate Declarations doc]
           docs  => [vcat [header "Hints"
                    , annotate Declarations $
                        vcat $ map (indent 2) docs]]

||| Look up implementations corresponding to the named type
getHintsForType : {auto c : Ref Ctxt Defs} ->
                  {auto s : Ref Syn SyntaxInfo} ->
                  Name -> Core (List (Doc IdrisDocAnn))
getHintsForType nty
    = do log "doc.data" 10 $ "Looking at \{show nty}"
         getImplDocs $ \ ty =>
           do let nms = allGlobals ty
              log "doc.data" 10 $ String.unlines
                [ "Candidate: " ++ show ty
                , "Containing names: " ++ show nms
                ]
              pure $ isJust (lookup nty nms)

||| Look up implementations corresponding to the primitive type
getHintsForPrimitive : {auto c : Ref Ctxt Defs} ->
                       {auto s : Ref Syn SyntaxInfo} ->
                       Constant -> Core (List (Doc IdrisDocAnn))
getHintsForPrimitive c
    = do log "doc.data" 10 $ "Looking at \{show c}"
         getImplDocs $ \ ty =>
           do let nms = allConstants ty
              log "doc.data" 10 $ String.unlines
                [ "Candidate: " ++ show ty
                , "Containing constants: " ++ show nms
                ]
              pure $ contains c nms

export
getDocsForPrimitive : {auto c : Ref Ctxt Defs} ->
                      {auto s : Ref Syn SyntaxInfo} ->
                      Constant -> Core (Doc IdrisDocAnn)
getDocsForPrimitive constant = do
    let (_, type) = checkPrim EmptyFC constant
    let typeString = prettyTerm (PPrimVal EmptyFC constant)
                     <++> colon
                     <++> prettyTerm !(resugar [] type)
    hintsDoc <- getHintsForPrimitive constant
    pure $ vcat $ typeString
               :: indent 2 (primDoc constant)
               :: hintsDoc

  where
  primDoc : Constant -> Doc IdrisDocAnn
  primDoc (I i) = "Primitive signed int value (backend-dependent precision)"
  primDoc (I8 i) = "Primitive signed 8 bits value"
  primDoc (I16 i) = "Primitive signed 16 bits value"
  primDoc (I32 i) = "Primitive signed 32 bits value"
  primDoc (I64 i) = "Primitive signed 64 bits value"
  primDoc (BI i) = "Primitive unsigned int value (backend-dependent precision)"
  primDoc (B8 i) = "Primitive unsigned 8 bits value"
  primDoc (B16 i) = "Primitive unsigned 16 bits value"
  primDoc (B32 i) = "Primitive unsigned 32 bits value"
  primDoc (B64 i) = "Primitive unsigned 64 bits value"
  primDoc (Str s) = "Primitive string value"
  primDoc (Ch c) = "Primitive character value"
  primDoc (Db d) = "Primitive double value"
  primDoc WorldVal = "Primitive token for IO actions"

  primDoc IntType = "Primitive type of bounded signed integers (backend dependent size)"
  primDoc Int8Type = "Primitive type of 8 bits signed integers"
  primDoc Int16Type = "Primitive type of 16 bits signed integers"
  primDoc Int32Type = "Primitive type of 32 bits signed integers"
  primDoc Int64Type = "Primitive type of 64 bits signed integers"
  primDoc IntegerType = "Primitive type of unbounded signed integers"
  primDoc Bits8Type = "Primitive type of 8 bits unsigned integers"
  primDoc Bits16Type = "Primitive type of 16 bits unsigned integers"
  primDoc Bits32Type = "Primitive type of 32 bits unsigned integers"
  primDoc Bits64Type = "Primitive type of 64 bits unsigned integers"
  primDoc StringType = "Primitive type of strings"
  primDoc CharType = "Primitive type of characters"
  primDoc DoubleType = "Primitive type of double-precision floating-points"
  primDoc WorldType = "Primitive type of tokens for IO actions"

public export
data Config : Type where
  ||| Configuration of the printer for a name
  ||| @ showType    Do we show the type?
  ||| @ longNames   Do we print qualified names?
  ||| @ dropFirst   Do we drop the first argument in the type?
  ||| @ getTotality Do we print the totality status of the function?
  MkConfig : {default True  showType    : Bool} ->
             {default True  longNames   : Bool} ->
             {default False dropFirst   : Bool} ->
             {default True  getTotality : Bool} ->
             Config

||| Printer configuration for interface methods
||| * longNames turned off for interface methods because the namespace is
|||             already spelt out for the interface itself
||| * dropFirst turned on for interface methods because the first argument
|||             is always the interface constraint
||| * totality  turned off for interface methods because the methods themselves
|||             are just projections out of a record and so are total
export
methodsConfig : Config
methodsConfig
  = MkConfig {showType = True}
             {longNames = False}
             {dropFirst = True}
             {getTotality = False}

export
shortNamesConfig : Config
shortNamesConfig
  = MkConfig {showType = True}
             {longNames = False}
             {dropFirst = False}
             {getTotality = True}

export
justUserDoc : Config
justUserDoc
  = MkConfig {showType = False}
             {longNames = False}
             {dropFirst = True}
             {getTotality = False}

export
getDocsForName : {auto o : Ref ROpts REPLOpts} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 FC -> Name -> Config -> Core (Doc IdrisDocAnn)
getDocsForName fc n config
    = do syn <- get Syn
         defs <- get Ctxt
         let extra = case nameRoot n of
                       "-" => [NS numNS (UN $ Basic "negate")]
                       _ => []
         resolved <- lookupCtxtName n (gamma defs)
         let all@(_ :: _) = extra ++ map fst resolved
             | _ => undefinedName fc n
         let ns@(_ :: _) = concatMap (\n => lookupName n (defDocstrings syn)) all
             | [] => pure emptyDoc
         docs <- traverse (showDoc config) ns
         pure $ vcat docs
  where

    showDoc : Config -> (Name, String) -> Core (Doc IdrisDocAnn)

    -- Avoid generating too much whitespace by not returning a single empty line
    reflowDoc : String -> List (Doc IdrisDocAnn)
    reflowDoc "" = []
    reflowDoc str = map (indent 2 . reflow) (forget $ Extra.lines str)

    showTotal : Name -> Totality -> Doc IdrisDocAnn
    showTotal n tot
        = case isTerminating tot of
               Unchecked => ""
               _ => header "Totality" <++> pretty tot

    getDConDoc : Name -> Core (Doc IdrisDocAnn)
    getDConDoc con
        = do defs <- get Ctxt
             Just def <- lookupCtxtExact con (gamma defs)
                  -- should never happen, since we know that the DCon exists:
                  | Nothing => pure Empty
             syn <- get Syn
             ty <- resugar [] =<< normaliseHoles defs [] (type def)
             let conWithTypeDoc = annotate (Decl con) (hsep [dCon con (prettyName con), colon, prettyTerm ty])
             case lookupName con (defDocstrings syn) of
               [(n, "")] => pure conWithTypeDoc
               [(n, str)] => pure $ vcat
                    [ conWithTypeDoc
                    , annotate DocStringBody
                    $ annotate UserDocString
                    $ vcat $ reflowDoc str
                    ]
               _ => pure conWithTypeDoc

    ||| The name corresponds to an implementation, typeset its type accordingly
    getImplDoc : Name -> Core (List (Doc IdrisDocAnn))
    getImplDoc n
        = do defs <- get Ctxt
             Just def <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure []
             ty <- resugar [] =<< normaliseHoles defs [] (type def)
             pure [annotate (Decl n) $ prettyTerm ty]

    getMethDoc : Method -> Core (List (Doc IdrisDocAnn))
    getMethDoc meth
        = do syn <- get Syn
             let [nstr] = lookupName meth.name (defDocstrings syn)
                  | _ => pure []
             pure <$> showDoc methodsConfig nstr

    getInfixDoc : Name -> Core (List (Doc IdrisDocAnn))
    getInfixDoc n
        = do let Just (Basic n) = userNameRoot n
                    | _ => pure []
             let Just (fixity, assoc) = S.lookup n (infixes !(get Syn))
                    | Nothing => pure []
             pure $ pure $ hsep
                  [ pretty (show fixity)
                  , "operator,"
                  , "level"
                  , pretty (show assoc)
                  ]

    getPrefixDoc : Name -> Core (List (Doc IdrisDocAnn))
    getPrefixDoc n
        = do let Just (Basic n) = userNameRoot n
                    | _ => pure []
             let Just assoc = S.lookup n (prefixes !(get Syn))
                    | Nothing => pure []
             pure $ ["prefix operator, level" <++> pretty (show assoc)]

    getFixityDoc : Name -> Core (List (Doc IdrisDocAnn))
    getFixityDoc n =
      pure $ case toList !(getInfixDoc n) ++ toList !(getPrefixDoc n) of
        []  => []
        [f] => [header "Fixity Declaration" <++> f]
        fs  => [header "Fixity Declarations" <+> Line <+>
                 indent 2 (vcat fs)]

    getIFaceDoc : (Name, IFaceInfo) -> Core (Doc IdrisDocAnn)
    getIFaceDoc (n, iface)
        = do let params =
                case params iface of
                     [] => []
                     ps => [hsep (header "Parameters" :: punctuate comma (map (pretty . show) ps))]
             let constraints =
                case !(traverse (pterm . map defaultKindedName) (parents iface)) of
                     [] => []
                     ps => [hsep (header "Constraints" :: punctuate comma (map (pretty . show) ps))]
             let icon = case dropNS (iconstructor iface) of
                          DN _ _ => [] -- machine inserted
                          nm => [hsep [header "Constructor", dCon nm (prettyName nm)]]
             mdocs <- traverse getMethDoc (methods iface)
             let meths = case concat mdocs of
                           [] => []
                           docs => [vcat [header "Methods", annotate Declarations $ vcat $ map (indent 2) docs]]
             sd <- getSearchData fc False n
             idocs <- case hintGroups sd of
                           [] => pure (the (List (List (Doc IdrisDocAnn))) [])
                           ((_, tophs) :: _) => traverse getImplDoc tophs
             let insts = case concat idocs of
                           [] => []
                           [doc] => [header "Implementation" <++> annotate Declarations doc]
                           docs => [vcat [header "Implementations"
                                   , annotate Declarations $ vcat $ map (indent 2) docs]]
             pure (vcat (params ++ constraints ++ icon ++ meths ++ insts))

    getFieldDoc : Name -> Core (Doc IdrisDocAnn)
    getFieldDoc nm
      = do syn <- get Syn
           defs <- get Ctxt
           Just def <- lookupCtxtExact nm (gamma defs)
                -- should never happen, since we know that the DCon exists:
                | Nothing => pure Empty
           ty <- resugar [] =<< normaliseHoles defs [] (type def)
           let prettyName = prettyName nm
           let projDecl = annotate (Decl nm) $ hsep [ fun nm prettyName, colon, prettyTerm ty ]
           case lookupName nm (defDocstrings syn) of
                [(_, "")] => pure projDecl
                [(_, str)] =>
                  pure $ vcat [ projDecl
                              , annotate DocStringBody
                              $ annotate UserDocString
                              $ vcat $ reflowDoc str
                              ]
                _ => pure projDecl

    getFieldsDoc : Name -> Core (Maybe (Doc IdrisDocAnn))
    getFieldsDoc recName
      = do let (Just ns, n) = displayName recName
               | _ => pure Nothing
           let recNS = ns <.> mkNamespace n
           defs <- get Ctxt
           let fields = getFieldNames (gamma defs) recNS
           syn <- get Syn
           case fields of
             [] => pure Nothing
             [proj] => pure $ Just $ header "Projection" <++> annotate Declarations !(getFieldDoc proj)
             projs => pure $ Just $ vcat
                           [ header "Projections"
                           , annotate Declarations $ vcat $
                               map (indent 2) $ !(traverse getFieldDoc projs)
                           ]

    getExtra : Name -> GlobalDef -> Core (Maybe String, List (Doc IdrisDocAnn))
    getExtra n d = do
      do syn <- get Syn
         let [] = lookupName n (ifaces syn)
             | [ifacedata] => (Just "interface",) . pure <$> getIFaceDoc ifacedata
             | _ => pure (Nothing, []) -- shouldn't happen, we've resolved ambiguity by now
         case definition d of
           PMDef _ _ _ _ _ => pure (Nothing, [showTotal n (totality d)])
           TCon _ _ _ _ _ _ cons _ =>
             do let tot = [showTotal n (totality d)]
                cdocs <- traverse (getDConDoc <=< toFullNames) cons
                cdoc <- case cdocs of
                  [] => pure (Just "data", [])
                  [doc] =>
                    let cdoc = header "Constructor" <++> annotate Declarations doc in
                    case !(getFieldsDoc n) of
                      Nothing => pure (Just "data", [cdoc])
                      Just fs => pure (Just "record", cdoc :: [fs])
                  docs => pure (Just "data"
                               , [vcat [header "Constructors"
                                       , annotate Declarations $
                                           vcat $ map (indent 2) docs]])
                idoc <- getHintsForType n
                pure (map (\ cons => tot ++ cons ++ idoc) cdoc)
           _ => pure (Nothing, [])

    showDoc (MkConfig {showType, longNames, dropFirst, getTotality}) (n, str)
        = do defs <- get Ctxt
             Just def <- lookupCtxtExact n (gamma defs)
                  | Nothing => undefinedName fc n
             -- First get the extra stuff because this also tells us whether a
             -- definition is `data`, `record`, or `interface`.
             (typ, extra) <- ifThenElse getTotality
                               (getExtra n def)
                               (pure (Nothing, []))

             -- Then form the type declaration
             ty <- resugar [] =<< normaliseHoles defs [] (type def)
             -- when printing e.g. interface methods there is no point in
             -- repeating the interface's name
             let ty = ifThenElse (not dropFirst) ty $ case ty of
                        PPi _ _ AutoImplicit _ _ sc => sc
                        _ => ty
             nm <- aliasName n
             -- when printing e.g. interface methods there is no point in
             -- repeating the namespace the interface lives in
             let cat = showCategory Syntax def
             let nm = prettyKindedName typ $ cat
                    $ ifThenElse longNames (pretty (show nm)) (prettyName nm)
             let deprecated = if Deprecate `elem` def.flags
                                 then annotate Deprecation "=DEPRECATED=" <+> line else emptyDoc
             let docDecl = deprecated <+> annotate (Decl n) (hsep [nm, colon, prettyTerm ty])

             -- Finally add the user-provided docstring
             let docText = let docs = reflowDoc str in
                           annotate UserDocString (vcat docs)
                           <$ guard (not $ null docs)
             fixes <- getFixityDoc n
             let docBody =
                  let docs = maybe id (::) docText
                           $ map (indent 2) (extra ++ fixes)
                  in annotate DocStringBody
                     (concatWith (\l, r => l <+> hardline <+> r) docs)
                     <$ guard (not (null docs))
             let maybeDocDecl = [docDecl | showType]
             pure . vcat . catMaybes $ maybeDocDecl :: (map Just $ docBody)

export
getDocsForPTerm : {auto o : Ref ROpts REPLOpts} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto s : Ref Syn SyntaxInfo} ->
                  PTerm -> Core (Doc IdrisDocAnn)
getDocsForPTerm (PRef fc name) = getDocsForName fc name MkConfig
getDocsForPTerm (PPrimVal _ c) = getDocsForPrimitive c
getDocsForPTerm (PType _) = pure $ vcat
  [ "Type : Type"
  , indent 2 "The type of all types is Type. The type of Type is Type."
  ]
getDocsForPTerm (PString _ _) = pure $ vcat
  [ "String Literal"
  , indent 2 "Desugars to a fromString call"
  ]
getDocsForPTerm (PList _ _ _) = pure $ vcat
  [ "List Literal"
  , indent 2 "Desugars to (::) and Nil"
  ]
getDocsForPTerm (PSnocList _ _ _) = pure $ vcat
  [ "SnocList Literal"
  , indent 2 "Desugars to (:<) and Lin"
  ]
getDocsForPTerm (PPair _ _ _) = pure $ vcat
  [ "Pair Literal"
  , indent 2 "Desugars to MkPair or Pair"
  ]
getDocsForPTerm (PDPair _ _ _ _ _) = pure $ vcat
  [ "Dependant Pair Literal"
  , indent 2 "Desugars to MkDPair or DPair"
  ]
getDocsForPTerm (PUnit _) = pure $ vcat
  [ "Unit Literal"
  , indent 2 "Desugars to MkUnit or Unit"
  ]
getDocsForPTerm pterm = pure $
  "Docs not implemented for" <++> pretty (show pterm) <++> "yet"

export
getDocs : {auto o : Ref ROpts REPLOpts} ->
          {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          DocDirective -> Core (Doc IdrisDocAnn)
getDocs (APTerm ptm) = getDocsForPTerm ptm
getDocs (Symbol k) = pure $ getDocsForSymbol k
getDocs (Keyword k) = pure $ getDocsForKeyword k


summarise : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            Name -> Core (Doc IdrisDocAnn)
summarise n -- n is fully qualified
    = do syn <- get Syn
         defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
             | _ => pure ""
         ty <- normaliseHoles defs [] (type def)
         pure $ showCategory Syntax def (prettyName n)
              <++> colon <++> hang 0 (prettyTerm !(resugar [] ty))

-- Display all the exported names in the given namespace
export
getContents : {auto o : Ref ROpts REPLOpts} ->
              {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Namespace -> Core (Doc IdrisDocAnn)
getContents ns
   = -- Get all the names, filter by any that match the given namespace
     -- and are visible, then display with their type
     do defs <- get Ctxt
        ns <- allNames (gamma defs)
        let allNs = filter inNS ns
        allNs <- filterM (visible defs) allNs
        vsep <$> traverse summarise (sort allNs)
  where
    visible : Defs -> Name -> Core Bool
    visible defs n
        = do Just def <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure False
             pure (visibility def /= Private)

    inNS : Name -> Bool
    inNS (NS xns (UN _)) = ns `isParentOf` xns
    inNS _ = False
