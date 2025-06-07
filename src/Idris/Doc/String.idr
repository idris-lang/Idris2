module Idris.Doc.String

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.TT
import Core.TT.Traversals

import Idris.Doc.Display
import Idris.Pretty
import Idris.REPL.Opts
import Idris.Resugar
import Idris.Syntax
import Idris.Syntax.Views

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
import Libraries.Data.WithDefault

import public Libraries.Text.PrettyPrint.Prettyprinter
import public Libraries.Text.PrettyPrint.Prettyprinter.Util

import Parser.Lexer.Source

import public Idris.Doc.Annotations
import Idris.Doc.Keywords
import Idris.Doc.Brackets

%default covering

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
         update Syn { defDocstrings  $= addName n doc,
                      saveDocstrings $= insert n () }

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
         update Syn { defDocstrings  $= addName n' doc,
                      saveDocstrings $= insert n' () }

prettyName : Name -> Doc IdrisDocAnn
prettyName n =
  case userNameRoot n of
    -- shouldn't happen: we only show UN anyways...
    Nothing => pretty0 (nameRoot n)
    Just un => if isOpUserName un then parens (pretty0 un) else pretty0 un

prettyKindedName : Maybe String -> Doc IdrisDocAnn -> Doc IdrisDocAnn
prettyKindedName Nothing   nm = nm
prettyKindedName (Just kw) nm
  = annotate (Syntax Keyword) (pretty0 kw) <++> nm

export
prettyType : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             (IdrisSyntax -> ann) -> ClosedTerm -> Core (Doc ann)
prettyType syn ty = do
  defs <- get Ctxt
  ty <- normaliseHoles defs Env.empty ty
  ty <- toFullNames ty
  ty <- resugar Env.empty ty
  pure (prettyBy syn ty)

||| Look up implementations
getImplDocs : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              (keep : ClosedTerm -> Core Bool) ->
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
              ty <- toFullNames !(normaliseHoles defs Env.empty (type def))
              True <- keep ty
                | False => pure []
              ty <- resugar Env.empty ty
              pure [annotate (Decl impl) $ prettyBy Syntax ty]
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
              log "doc.data" 10 $ unlines
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
              log "doc.data" 10 $ unlines
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
    let typeString = prettyBy Syntax constant
                     <++> colon
                     <++> prettyBy Syntax !(resugar Env.empty type)
    hintsDoc <- getHintsForPrimitive constant
    pure $ vcat $ typeString
               :: indent 2 (primDoc constant)
               :: hintsDoc

  where
  primTyDoc : PrimType -> Doc IdrisDocAnn
  primTyDoc IntType = "Primitive type of bounded signed integers (backend dependent size)"
  primTyDoc Int8Type = "Primitive type of 8 bits signed integers"
  primTyDoc Int16Type = "Primitive type of 16 bits signed integers"
  primTyDoc Int32Type = "Primitive type of 32 bits signed integers"
  primTyDoc Int64Type = "Primitive type of 64 bits signed integers"
  primTyDoc IntegerType = "Primitive type of unbounded signed integers"
  primTyDoc Bits8Type = "Primitive type of 8 bits unsigned integers"
  primTyDoc Bits16Type = "Primitive type of 16 bits unsigned integers"
  primTyDoc Bits32Type = "Primitive type of 32 bits unsigned integers"
  primTyDoc Bits64Type = "Primitive type of 64 bits unsigned integers"
  primTyDoc StringType = "Primitive type of strings"
  primTyDoc CharType = "Primitive type of characters"
  primTyDoc DoubleType = "Primitive type of double-precision floating-points"
  primTyDoc WorldType = "Primitive type of tokens for IO actions"

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
  primDoc (PrT t) = primTyDoc t
  primDoc WorldVal = "Primitive token for IO actions"

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

    reflowDoc : String -> List (Doc IdrisDocAnn)
    reflowDoc str = map (indent 2 . pretty0) (lines str)

    showTotal : Totality -> Maybe (Doc IdrisDocAnn)
    showTotal tot
        = case isTerminating tot of
               Unchecked => Nothing
               _ => pure (header "Totality" <++> annotate (Syntax Keyword) (pretty0 tot))

    showVisible : Visibility -> Doc IdrisDocAnn
    showVisible vis = header "Visibility" <++> annotate (Syntax Keyword) (pretty0 vis)

    getDConDoc : {default True showType : Bool} -> Name -> Core (Doc IdrisDocAnn)
    getDConDoc con
        = do defs <- get Ctxt
             Just def <- lookupCtxtExact con (gamma defs)
                  -- should never happen, since we know that the DCon exists:
                  | Nothing => pure Empty
             syn <- get Syn
             ty <- prettyType Syntax (type def)
             let conWithTypeDoc
                   = annotate (Decl con)
                   $ ifThenElse showType
                       (hsep [dCon con (prettyName con), colon, ty])
                       (dCon con (prettyName con))
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
             ty <- prettyType Syntax (type def)
             pure [annotate (Decl n) ty]

    getMethDoc : Method -> Core (List (Doc IdrisDocAnn))
    getMethDoc meth
        = do syn <- get Syn
             let [nstr] = lookupName meth.name (defDocstrings syn)
                  | _ => pure []
             pure <$> showDoc methodsConfig nstr

    getInfixDoc : Name -> Core (List (Doc IdrisDocAnn))
    getInfixDoc n
        = let names = lookupName (UN $ Basic $ nameRoot n) (infixes !(get Syn))
          in pure $ map printName names
        where
          printName : (Name, FC, Fixity, Nat) -> (Doc IdrisDocAnn)
          printName (name,  loc, fixity, assoc) =
            -- todo,  change display as "infix operator (++)
             hsep
                  [ pretty0 (show fixity)
                  , "operator,"
                  , "level"
                  , pretty0 (show assoc)
                  ]

    getPrefixDoc : Name -> Core (List (Doc IdrisDocAnn))
    getPrefixDoc n
        = let names = lookupName (UN $ Basic $ nameRoot n) (prefixes !(get Syn))
          in pure $ map printPrefixName names
          where
            printPrefixName : (Name, FC, Nat) -> Doc IdrisDocAnn
            printPrefixName (_, _, assoc) = "prefix operator, level" <++> pretty0 (show assoc)

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
                     ps => [hsep (header "Parameters" :: punctuate comma (map pretty0 ps))]
             let constraints =
                case !(traverse (pterm . map defaultKindedName) (parents iface)) of
                     [] => []
                     ps => [hsep (header "Constraints" :: punctuate comma (map (prettyBy Syntax) ps))]
             icon <- do cName <- toFullNames (iconstructor iface)
                        case dropNS cName of
                          UN{} => do doc <- getDConDoc {showType = False} cName
                                     pure $ [header "Constructor" <++> annotate Declarations doc]
                          _ => pure [] -- machine inserted
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
           ty <- prettyType Syntax (type def)
           let projDecl = annotate (Decl nm) $
                            reAnnotate Syntax (prettyRig def.multiplicity) <+> hsep
                            [ fun nm (prettyName nm), colon, ty ]
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
           PMDef _ _ _ _ _ => pure ( Nothing
                                   , catMaybes [ showTotal (totality d)
                                               , pure (showVisible (collapseDefault $ visibility d))])
           TCon _ _ _ _ _ _ cons _ =>
             do let tot = catMaybes [ showTotal (totality d)
                                    , pure (showVisible (collapseDefault $ visibility d))]
                cdocs <- traverse (getDConDoc <=< toFullNames) (fromMaybe [] cons)
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
             ty <- resugar Env.empty =<< normaliseHoles defs Env.empty (type def)
             -- when printing e.g. interface methods there is no point in
             -- repeating the interface's name
             let ty = ifThenElse (not dropFirst) ty $ case ty of
                        PPi _ _ AutoImplicit _ _ sc => sc
                        _ => ty
             nm <- aliasName n
             let prig = reAnnotate Syntax $ prettyRig def.multiplicity
             let cat = showCategory Syntax def
             let nm = prettyKindedName typ $ cat
                    $ ifThenElse longNames (pretty0 (show nm)) (prettyName nm)
             let deprecated = if Context.Deprecate `elem` def.flags
                                 then annotate Deprecation "=DEPRECATED=" <+> line else emptyDoc
             let docDecl = deprecated
                     <+> annotate (Decl n) (hsep [prig <+> nm, colon, prettyBy Syntax ty])

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
getDocsForImplementation :
  {auto s : Ref Syn SyntaxInfo} ->
  {auto c : Ref Ctxt Defs} ->
  PTerm -> Core (Maybe (Doc IdrisSyntax))
getDocsForImplementation t = do
  -- the term better be of the shape (I e1 e2 e3) where I is a name
  let (PRef fc intf, args) = getFnArgs id t
    | _ => pure Nothing
  -- That name (I) better be the name of an interface
  syn <- get Syn
  -- Important: we shadow intf with the fully qualified version returned by lookupName
  let [(intf, _)] = lookupName intf (ifaces syn)
    | _ => pure Nothing
  -- Now lookup the declared implementations for that interface
  -- For now we only look at the top list
  ((_, tophs) :: _) <- hintGroups <$> getSearchData fc False intf
    | _ => pure Nothing
  defs <- get Ctxt
  impls <- map catMaybes $ for tophs $ \ hint => do
    -- get the return type of all the candidate hints
    Just (ix, def) <- lookupCtxtExactI hint (gamma defs)
      | Nothing => pure Nothing
    ty <- resugar Env.empty =<< normaliseHoles defs Env.empty (type def)
    let (_, retTy) = underPis ty
    -- try to see whether it approximates what we are looking for
    -- we throw the head away because it'll be the interface name (I)
    let (_, cargs) = getFnArgs defaultKindedName retTy
    bs <- for (zip args cargs) $ \ (arg, carg) => do
      -- For now we only compare the heads of the arguments because we expect
      -- we are interested in implementations of the form
      -- Eq (List a), Functor (Vect n), etc.
      -- In the future we could be more discriminating and make sure we only
      -- retain implementations whose type is fully compatible.

      -- TODO: check the Args have the same shape before unArgging?
      let ((PRef fc hd, _), (PRef _ chd, _)) = ( getFnArgs id (unArg arg), getFnArgs defaultKindedName (unArg carg))
        | ((PPrimVal _ c, _), (PPrimVal _ c', _)) => pure (c == c')
        | ((PType _, _), (PType _, _)) => pure True
        | _ => pure False
      -- if the names match on the nose we can readily say True
      let False = dropNS hd == dropNS (fullName chd)
        | True => pure True
      -- otherwise we check hd is unknown in which case we're happy to
      -- declare it to be a placeholder name and that it could possibly
      -- unify e.g. a & b in (List a) vs. (List b)
      existing <- lookupCtxtName hd (gamma defs)
      log "doc.implementation" 50 $ unwords
        [ "Mismatch between \{show hd} and \{show chd},"
        , "checking whether \{show hd} exists:"
        , "\{show $ length existing} candidates"
        ]
      let [] = existing
        | _ => pure False
      -- If the name starts with an uppercase letter it's probably a misspelt constructor name
      whenJust ((isUN >=> (isBasic . snd) >=> strUncons >=> (guard . isUpper . fst)) hd) $ \ _ =>
        undefinedName fc hd
      pure True
    -- all arguments better be valid approximations
    let True = all id bs
      | False => pure Nothing
    pure (Just (hint, ix, def))
  case impls of
    [] => pure $ Just $ "Could not find an implementation for" <++> pretty0 (show t) --hack
    _ => do ds <- traverse (displayImpl defs) impls
            pure $ Just $ vcat ds

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
getDocsForPTerm (PString _ _ _) = pure $ vcat
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
getDocsForPTerm (PUnquote _ _) = pure $ vcat $
  header "Unquotes" :: ""
  :: map (indent 2) [
  """
  Unquotes allows us to use TTImp expressions inside a quoted expression.
  This is useful when we want to add some computed TTImp while building up
  complex expressions.

  ```idris
  module Quote

  import Language.Reflection

  foo : TTImp -> TTImp
  foo expr = `(either ~(expr) x y)
  ```
  """]
getDocsForPTerm (PDelayed _ LLazy _) = pure $ vcat $
  header "Laziness annotation" :: ""
  :: map (indent 2) [
  """
  Indicates that the values of the type should not be computed until absolutely
  necessary.

  Also causes the compiler to automatically insert Delay/Force calls
  respectively wherever a computation can be postponed and where a value is
  necessary. This can be disabled using the `%auto_lazy off` pragma.
  """
  ]
getDocsForPTerm (PDelayed _ LInf  _) = pure $ vcat $
  header "Codata (infinite data type) annotation" :: ""
  :: map (indent 2) [
  """
  Indicates that the data type may be potentially infinite, e.g. Data.Stream.
  If the data type IS infinite, it has to be productive, i.e. there has to be at
  least one non-empty, finite prefix of the type.

  Also causes the compiler to automatically insert Delay/Force calls
  respectively wherever the next part of a potentially infinite structure
  occurs, and where we need to look under the next finite prefix of the
  structure. This can be disabled using the `%auto_lazy off` pragma.
  """
  ]
getDocsForPTerm (PDelay _ _) = pure $ vcat $
  header "Laziness compiler primitive" :: ""
  :: map (indent 2) [
  """
  For `Lazy` types: postpones the computation until a `Force` requires its
                    result.
  For `Inf` types: does not try to deconstruct the next part of the codata
                   (potentially infinite data structure).

  Automatically inserted by the compiler unless `%auto_lazy off` is set.
  """
  ]
getDocsForPTerm (PForce _ _) = pure $ vcat $
  header "Laziness compiler primitive" :: ""
  :: map (indent 2) [
  """
  For `Lazy` types: requires the result of a postponed calculation to be
                    evaluated (see `Delay`).
  For `Inf` types: deconstructs the next part of the codata (potentially
                   infinite data structure).

  Automatically inserted by the compiler unless `%auto_lazy off` is set.
  """
  ]
getDocsForPTerm pterm = pure $ "Docs not implemented for" <++> pretty0 (show pterm) <++> "yet"

export
getDocs : {auto o : Ref ROpts REPLOpts} ->
          {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          DocDirective -> Core (Doc IdrisDocAnn)
getDocs (APTerm ptm) = getDocsForPTerm ptm
getDocs (Symbol k) = pure $ getDocsForSymbol k
getDocs (Bracket bracket) = pure $ getDocsForBracket bracket
getDocs (Keyword k) = pure $ getDocsForKeyword k
getDocs (AModule mod) = do
  syn  <- get Syn
  let Just modDoc = lookup mod (modDocstrings syn)
    | _ => throw (ModuleNotFound replFC mod)
  pure (pretty0 modDoc)

summarise : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            Name -> Core (Doc IdrisDocAnn)
summarise n -- n is fully qualified
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
             | _ => pure ""
         ty <- prettyType Syntax (type def)
         pure $ reAnnotate Syntax (prettyRig def.multiplicity)
            <+> hsep [ showCategory Syntax def (prettyName n)
                     , colon, hang 0 ty
                     ]

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
             pure (collapseDefault (visibility def) /= Private)

    inNS : Name -> Bool
    inNS (NS xns (UN _)) = ns `isParentOf` xns
    inNS _ = False
