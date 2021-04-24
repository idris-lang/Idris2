module Idris.DocString

import Core.Context
import Core.Core
import Core.Env
import Core.TT

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

public export
data IdrisDocAnn
  = TCon
  | DCon
  | Fun
  | Header

export
styleAnn : IdrisDocAnn -> AnsiStyle
styleAnn TCon = color BrightBlue
styleAnn DCon = color BrightRed
styleAnn Fun = color BrightGreen
styleAnn Header = underline

export
tCon : Doc IdrisDocAnn -> Doc IdrisDocAnn
tCon = annotate TCon

export
dCon : Doc IdrisDocAnn -> Doc IdrisDocAnn
dCon = annotate DCon

export
fun : Doc IdrisDocAnn -> Doc IdrisDocAnn
fun = annotate Fun

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

export
getDocsForName : {auto o : Ref ROpts REPLOpts} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 FC -> Name -> Core String
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
             | [] => pure ("No documentation for " ++ show n)
         docs <- traverse showDoc ns
         render styleAnn (vcat (punctuate Line docs))
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

    getDConDoc : Name -> Core (List (Doc IdrisDocAnn))
    getDConDoc con
        = do defs <- get Ctxt
             Just def <- lookupCtxtExact con (gamma defs)
                  | Nothing => pure []
             syn <- get Syn
             let [(n, str)] = lookupName con (docstrings syn)
                  | _ => pure []
             ty <- resugar [] =<< normaliseHoles defs [] (type def)
             pure $ pure $ vcat $
               hsep [dCon (pretty (nameRoot n)), colon, pretty (show ty)]
               :: reflowDoc str

    getImplDoc : Name -> Core (List (Doc IdrisDocAnn))
    getImplDoc n
        = do defs <- get Ctxt
             Just def <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure []
             ty <- resugar [] =<< normaliseHoles defs [] (type def)
             pure [pretty (show ty)]

    getMethDoc : Method -> Core (List (Doc IdrisDocAnn))
    getMethDoc meth
        = do syn <- get Syn
             let [(n, str)] = lookupName meth.name (docstrings syn)
                  | _ => pure []
             ty <- pterm meth.type
             let nm = nameRoot meth.name
             pure $ pure $ vcat $
               [hsep [fun (pretty nm), colon, pretty (show ty)]]
               ++ toList (indent 2 . pretty . show <$> meth.totalReq)
               ++ reflowDoc str

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
                           docs => [vcat (header "Methods" :: map (indent 2) docs)]
             sd <- getSearchData fc False n
             idocs <- case hintGroups sd of
                           [] => pure (the (List (List (Doc IdrisDocAnn))) [])
                           ((_, tophs) :: _) => traverse getImplDoc tophs
             let insts = case concat idocs of
                           [] => []
                           [doc] => [header "Implementation" <++> doc]
                           docs => [vcat (header "Implementations"
                                           :: map (indent 2) docs)]
             pure (vcat (params ++ constraints ++ meths ++ insts))

    getExtra : Name -> GlobalDef -> Core (List (Doc IdrisDocAnn))
    getExtra n d
        = do syn <- get Syn
             let [] = lookupName n (ifaces syn)
                 | [ifacedata] => pure <$> getIFaceDoc ifacedata
                 | _ => pure [] -- shouldn't happen, we've resolved ambiguity by now
             case definition d of
               PMDef _ _ _ _ _
                   => pure [showTotal n (totality d)]
               TCon _ _ _ _ _ _ cons _
                   => do let tot = [showTotal n (totality d)]
                         cdocs <- traverse (getDConDoc <=< toFullNames) cons
                         let cdoc = case concat cdocs of
                              [] => []
                              [doc] => [header "Constructor" <++>  doc]
                              docs => [vcat (header "Constructors" :: map (indent 2) docs)]
                         pure (tot ++ cdoc)
               _ => pure []

    showCategory : GlobalDef -> Doc IdrisDocAnn -> Doc IdrisDocAnn
    showCategory d = case definition d of
      TCon _ _ _ _ _ _ _ _ => tCon
      DCon _ _ _ => dCon
      PMDef _ _ _ _ _ => fun
      ForeignDef _ _ => fun
      Builtin _ => fun
      _ => id

    showDoc : (Name, String) -> Core (Doc IdrisDocAnn)
    showDoc (n, str)
        = do defs <- get Ctxt
             Just def <- lookupCtxtExact n (gamma defs)
                  | Nothing => undefinedName fc n
             ty <- resugar [] =<< normaliseHoles defs [] (type def)
             let cat = showCategory def
             nm <- aliasName n
             let doc = vcat $
                    (hsep [cat (pretty (show nm)), colon, pretty (show ty)])
                    :: reflowDoc str
             extra <- getExtra n def
             fixes <- getFixityDoc n
             pure (vcat (doc :: map (indent 2) (extra ++ fixes)))

export
getDocsForPTerm : {auto o : Ref ROpts REPLOpts} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto s : Ref Syn SyntaxInfo} ->
                  PTerm -> Core (List String)
getDocsForPTerm (PRef fc name) = pure <$> getDocsForName fc name
getDocsForPTerm (PPrimVal _ constant) = getDocsForPrimitive constant
getDocsForPTerm (PType _) = pure ["Type : Type\n\tThe type of all types is Type. The type of Type is Type."]
getDocsForPTerm (PString _ _) = pure ["String Literal\n\tDesugars to a fromString call"]
getDocsForPTerm (PList _ _) = pure ["List Literal\n\tDesugars to (::) and Nil"]
getDocsForPTerm (PPair _ _ _) = pure ["Pair Literal\n\tDesugars to MkPair or Pair"]
getDocsForPTerm (PDPair _ _ _ _) = pure ["Dependant Pair Literal\n\tDesugars to MkDPair or DPair"]
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
