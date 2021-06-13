module Idris.Doc.String

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.TT

import Idris.Pretty
import Idris.Pretty.Render
import Idris.REPL.Opts
import Idris.Resugar
import Idris.Syntax

import TTImp.TTImp
import TTImp.Elab.Prim

import Data.List
import Data.List1
import Data.Maybe
import Data.Strings

import Libraries.Data.ANameMap
import Libraries.Data.NameMap
import Libraries.Data.StringMap as S
import Libraries.Data.String.Extra

import Libraries.Control.ANSI.SGR
import public Libraries.Text.PrettyPrint.Prettyprinter
import public Libraries.Text.PrettyPrint.Prettyprinter.Util

import Parser.Lexer.Source

%default covering

public export
data IdrisDocAnn
  = TCon Name
  | DCon
  | Fun Name
  | Header
  | Declarations
  | Decl Name
  | DocStringBody
  | Syntax IdrisSyntax

export
styleAnn : IdrisDocAnn -> AnsiStyle
styleAnn (TCon _) = color BrightBlue
styleAnn DCon = color BrightRed
styleAnn (Fun _) = color BrightGreen
styleAnn Header = underline
styleAnn _ = []

export
tCon : Name -> Doc IdrisDocAnn -> Doc IdrisDocAnn
tCon n = annotate (TCon n)

export
dCon : Doc IdrisDocAnn -> Doc IdrisDocAnn
dCon = annotate DCon

export
fun : Name -> Doc IdrisDocAnn -> Doc IdrisDocAnn
fun n = annotate (Fun n)

export
header : Doc IdrisDocAnn -> Doc IdrisDocAnn
header d = annotate Header d <+> colon


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
         put Syn (record { docstrings $= addName n doc,
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
         put Syn (record { docstrings $= addName n' doc,
                           saveDocstrings $= insert n' () } syn)

export
getDocsForPrimitive : {auto c : Ref Ctxt Defs} ->
                      {auto s : Ref Syn SyntaxInfo} ->
                      Constant -> Core (List String)
getDocsForPrimitive constant = do
    let (_, type) = checkPrim EmptyFC constant
    let typeString = show constant ++ " : " ++ show !(resugar [] type)
    pure [typeString ++ "\n\tPrimitive"]

prettyTerm : PTerm -> Doc IdrisDocAnn
prettyTerm = reAnnotate Syntax . Idris.Pretty.prettyTerm

export
getDocsForName : {auto o : Ref ROpts REPLOpts} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 FC -> Name -> Core (Doc IdrisDocAnn)
getDocsForName fc n
    = do syn <- get Syn
         defs <- get Ctxt
         let extra = case nameRoot n of
                       "-" => [NS numNS (UN "negate")]
                       _ => []
         resolved <- lookupCtxtName n (gamma defs)
         let all@(_ :: _) = extra ++ map fst resolved
             | _ => undefinedName fc n
         let ns@(_ :: _) = concatMap (\n => lookupName n (docstrings syn)) all
             | [] => pure $ pretty ("No documentation for " ++ show n)
         docs <- traverse showDoc ns
         pure $ vcat (punctuate Line docs)
  where

    -- Avoid generating too much whitespace by not returning a single empty line
    reflowDoc : String -> List (Doc IdrisDocAnn)
    reflowDoc "" = []
    reflowDoc str = map (indent 2 . reflow) (forget $ Extra.lines str)

    showTotal : Name -> Totality -> Doc IdrisDocAnn
    showTotal n tot
        = case isTerminating tot of
               Unchecked => ""
               _ => header "Totality" <++> pretty tot

    prettyName : Name -> Doc IdrisDocAnn
    prettyName n =
      let root = nameRoot n in
      if isOpName n then parens (pretty root) else pretty root

    getDConDoc : Name -> Core (Doc IdrisDocAnn)
    getDConDoc con
        = do defs <- get Ctxt
             Just def <- lookupCtxtExact con (gamma defs)
                  -- should never happen, since we know that the DCon exists:
                  | Nothing => pure Empty
             syn <- get Syn
             ty <- resugar [] =<< normaliseHoles defs [] (type def)
             let conWithTypeDoc = annotate (Decl con) (hsep [dCon (prettyName con), colon, prettyTerm ty])
             let [(n, str)] = lookupName con (docstrings syn)
                  | _ => pure conWithTypeDoc
             pure $ vcat
               [ conWithTypeDoc
               , annotate DocStringBody $ vcat $ reflowDoc str
               ]

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
             let [(n, str)] = lookupName meth.name (docstrings syn)
                  | _ => pure []
             ty <- pterm meth.type
             let nm = prettyName meth.name
             pure $ pure $ vcat [
               annotate (Decl meth.name) (hsep [fun (meth.name) nm, colon, prettyTerm ty])
               , annotate DocStringBody $ vcat (
                 toList (indent 2 . pretty . show <$> meth.totalReq)
                 ++ reflowDoc str)
               ]

    getInfixDoc : Name -> Core (List (Doc IdrisDocAnn))
    getInfixDoc n
        = do let Just (fixity, assoc) = S.lookupName n (infixes !(get Syn))
                    | Nothing => pure []
             pure $ pure $ hsep
                  [ pretty (show fixity)
                  , "operator,"
                  , "level"
                  , pretty (show assoc)
                  ]

    getPrefixDoc : Name -> Core (List (Doc IdrisDocAnn))
    getPrefixDoc n
        = do let Just assoc = S.lookupName n (prefixes !(get Syn))
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
                case !(traverse pterm (parents iface)) of
                     [] => []
                     ps => [hsep (header "Constraints" :: punctuate comma (map (pretty . show) ps))]
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
             pure (vcat (params ++ constraints ++ meths ++ insts))

    getFieldDoc : Name -> Core (Doc IdrisDocAnn)
    getFieldDoc nm
      = do syn <- get Syn
           defs <- get Ctxt
           Just def <- lookupCtxtExact nm (gamma defs)
                -- should never happen, since we know that the DCon exists:
                | Nothing => pure Empty
           ty <- resugar [] =<< normaliseHoles defs [] (type def)
           let prettyName = pretty (nameRoot nm)
           let projDecl = hsep [ fun nm prettyName, colon, prettyTerm ty ]
           let [(_, str)] = lookupName nm (docstrings syn)
                  | _ => pure projDecl
           pure $ annotate (Decl nm)
                $ vcat [ projDecl
                       , annotate DocStringBody $ vcat (reflowDoc str)
                       ]

    getFieldsDoc : Name -> Core (List (Doc IdrisDocAnn))
    getFieldsDoc recName
      = do let (Just ns, n) = displayName recName
               | _ => pure []
           let recNS = ns <.> mkNamespace n
           defs <- get Ctxt
           let fields = getFieldNames (gamma defs) recNS
           syn <- get Syn
           case fields of
             [] => pure []
             [proj] => pure [header "Projection" <++> annotate Declarations !(getFieldDoc proj)]
             projs => pure [vcat [header "Projections"
                                 , annotate Declarations $
                                      vcat $ map (indent 2) $ !(traverse getFieldDoc projs)]]

    getExtra : Name -> GlobalDef -> Core (List (Doc IdrisDocAnn))
    getExtra n d = do
      do syn <- get Syn
         let [] = lookupName n (ifaces syn)
             | [ifacedata] => pure <$> getIFaceDoc ifacedata
             | _ => pure [] -- shouldn't happen, we've resolved ambiguity by now
         case definition d of
           PMDef _ _ _ _ _ => pure [showTotal n (totality d)]
           TCon _ _ _ _ _ _ cons _ =>
             do let tot = [showTotal n (totality d)]
                cdocs <- traverse (getDConDoc <=< toFullNames) cons
                cdoc <- case cdocs of
                  [] => pure []
                  [doc] => pure
                         $ (header "Constructor" <++> annotate Declarations doc)
                         :: !(getFieldsDoc n)
                  docs => pure [vcat [header "Constructors"
                                     , annotate Declarations $
                                         vcat $ map (indent 2) docs]]
                pure (tot ++ cdoc)
           _ => pure []

    showCategory : GlobalDef -> Doc IdrisDocAnn -> Doc IdrisDocAnn
    showCategory d = case definition d of
      TCon _ _ _ _ _ _ _ _ => tCon (fullname d)
      DCon _ _ _ => dCon
      PMDef _ _ _ _ _ => fun (fullname d)
      ForeignDef _ _ => fun (fullname d)
      Builtin _ => fun (fullname d)
      _ => id

    showDoc : (Name, String) -> Core (Doc IdrisDocAnn)
    showDoc (n, str)
        = do defs <- get Ctxt
             Just def <- lookupCtxtExact n (gamma defs)
                  | Nothing => undefinedName fc n
             ty <- resugar [] =<< normaliseHoles defs [] (type def)
             let cat = showCategory def
             nm <- aliasName n
             let docDecl = annotate (Decl n) (hsep [cat (pretty (show nm)), colon, prettyTerm ty])
             let docText = reflowDoc str
             extra <- getExtra n def
             fixes <- getFixityDoc n
             let docBody = annotate DocStringBody $ vcat $ docText ++ (map (indent 2) (extra ++ fixes))
             pure (vcat [docDecl, docBody])

export
getDocsForPTerm : {auto o : Ref ROpts REPLOpts} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto s : Ref Syn SyntaxInfo} ->
                  PTerm -> Core (List String)
getDocsForPTerm (PRef fc name) = pure $ [!(render styleAnn !(getDocsForName fc name))]
getDocsForPTerm (PPrimVal _ constant) = getDocsForPrimitive constant
getDocsForPTerm (PType _) = pure ["Type : Type\n\tThe type of all types is Type. The type of Type is Type."]
getDocsForPTerm (PString _ _) = pure ["String Literal\n\tDesugars to a fromString call"]
getDocsForPTerm (PList _ _ _) = pure ["List Literal\n\tDesugars to (::) and Nil"]
getDocsForPTerm (PSnocList _ _ _) = pure ["SnocList Literal\n\tDesugars to (:<) and Empty"]
getDocsForPTerm (PPair _ _ _) = pure ["Pair Literal\n\tDesugars to MkPair or Pair"]
getDocsForPTerm (PDPair _ _ _ _ _) = pure ["Dependant Pair Literal\n\tDesugars to MkDPair or DPair"]
getDocsForPTerm (PUnit _) = pure ["Unit Literal\n\tDesugars to MkUnit or Unit"]
getDocsForPTerm pterm = pure ["Docs not implemented for " ++ show pterm ++ " yet"]

summarise : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            Name -> Core String
summarise n -- n is fully qualified
    = do syn <- get Syn
         defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
             | _ => pure ""
         let doc = case lookupName n (docstrings syn) of
                        [(_, doc)] => case Extra.lines doc of
                                           ("" ::: _) => Nothing
                                           (d ::: _) => Just d
                        _ => Nothing
         ty <- normaliseHoles defs [] (type def)
         pure (nameRoot n ++ " : " ++ show !(resugar [] ty) ++
                  maybe "" (\d => "\n\t" ++ d) doc)

-- Display all the exported names in the given namespace
export
getContents : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Namespace -> Core (List String)
getContents ns
   = -- Get all the names, filter by any that match the given namespace
     -- and are visible, then display with their type
     do defs <- get Ctxt
        ns <- allNames (gamma defs)
        let allNs = filter inNS ns
        allNs <- filterM (visible defs) allNs
        traverse summarise (sort allNs)
  where
    visible : Defs -> Name -> Core Bool
    visible defs n
        = do Just def <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure False
             pure (visibility def /= Private)

    inNS : Name -> Bool
    inNS (NS xns (UN _)) = ns `isParentOf` xns
    inNS _ = False
