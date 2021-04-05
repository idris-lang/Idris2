module Idris.DocString

import Core.Context
import Core.Core
import Core.Env
import Core.TT

import Idris.Resugar
import Idris.Syntax

import TTImp.TTImp
import TTImp.Elab.Prim

import Libraries.Data.ANameMap
import Data.List
import Data.List1
import Data.Maybe
import Libraries.Data.NameMap
import Data.Strings
import Libraries.Data.String.Extra

%hide Data.Strings.lines
%hide Data.Strings.lines'
%hide Data.Strings.unlines
%hide Data.Strings.unlines'

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
getDocsForName : {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 FC -> Name -> Core (List String)
getDocsForName fc n
    = do syn <- get Syn
         defs <- get Ctxt
         all@(_ :: _) <- lookupCtxtName n (gamma defs)
             | _ => undefinedName fc n
         let ns@(_ :: _) = concatMap (\n => lookupName n (docstrings syn))
                                     (map fst all)
             | [] => pure ["No documentation for " ++ show n]
         traverse showDoc ns
  where
    addNL : String -> String
    addNL str = if trim str == "" then "" else str ++ "\n"

    indent : String -> String
    indent str = unlines $ map ("\t" ++) (forget $ lines str)

    showTotal : Name -> Totality -> String
    showTotal n tot
        = case isTerminating tot of
               Unchecked => ""
               _ => "\nTotality: " ++ show tot

    getConstructorDoc : Name -> Core (Maybe String)
    getConstructorDoc con
        = do defs <- get Ctxt
             Just def <- lookupCtxtExact con (gamma defs)
                  | Nothing => pure Nothing
             syn <- get Syn
             let [(n, str)] = lookupName con (docstrings syn)
                  | _ => pure Nothing
             ty <- normaliseHoles defs [] (type def)
             pure (Just (nameRoot n ++ " : " ++ show !(resugar [] ty)
                          ++ "\n" ++ addNL (indent str)))

    getImplDoc : Name -> Core (Maybe String)
    getImplDoc n
        = do defs <- get Ctxt
             Just def <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure Nothing
             ty <- normaliseHoles defs [] (type def)
             pure $ Just $ addNL $ indent $ show !(resugar [] ty)

    getMethDoc : Method -> Core (Maybe String)
    getMethDoc meth
        = do syn <- get Syn
             let [(n, str)] = lookupName meth.name (docstrings syn)
                  | _ => pure Nothing
             pure (Just (nameRoot meth.name ++ " : " ++ show !(pterm meth.type)
                          ++ maybe "" (\t => "\n" ++ show t) meth.totalReq
                          ++ "\n" ++ addNL (indent str)))

    getIFaceDoc : (Name, IFaceInfo) -> Core String
    getIFaceDoc (n, iface)
        = do let params =
                case params iface of
                     [] => ""
                     ps => "Parameters: " ++ showSep ", " (map show ps) ++ "\n"
             constraints <-
                case parents iface of
                     [] => pure ""
                     ps => do pts <- traverse pterm ps
                              pure ("Constraints: " ++
                                    showSep ", " (map show pts) ++ "\n")
             mdocs <- traverse getMethDoc (methods iface)
             let meths = case mapMaybe id mdocs of
                              [] => ""
                              docs => "\nMethods:\n" ++ concat docs
             sd <- getSearchData fc False n
             idocs <- case hintGroups sd of
                           [] => pure []
                           ((_, tophs) :: _) => traverse getImplDoc tophs
             let insts = case mapMaybe id idocs of
                              [] => ""
                              docs => "\nImplementations:\n" ++ concat docs
             pure (params ++ constraints ++ meths ++ insts)

    getExtra : Name -> GlobalDef -> Core String
    getExtra n d
        = do syn <- get Syn
             let [] = lookupName n (ifaces syn)
                 | [ifacedata] => getIFaceDoc ifacedata
                 | _ => pure "" -- shouldn't happen, we've resolved ambiguity by now
             case definition d of
               PMDef _ _ _ _ _
                   => pure (showTotal n (totality d))
               TCon _ _ _ _ _ _ cons _
                   => do cdocs <- traverse getConstructorDoc
                                           !(traverse toFullNames cons)
                         case mapMaybe id cdocs of
                              [] => pure ""
                              docs => pure $ "\nConstructors:\n" ++ concat docs
               _ => pure ""

    showDoc : (Name, String) -> Core String
    showDoc (n, str)
        = do defs <- get Ctxt
             Just def <- lookupCtxtExact n (gamma defs)
                  | Nothing => undefinedName fc n
             ty <- normaliseHoles defs [] (type def)
             let doc = show !(aliasName n) ++ " : " ++ show !(resugar [] ty)
                              ++ "\n" ++ addNL (indent str)
             extra <- getExtra n def
             pure (doc ++ extra)

export
getDocsForPTerm : {auto c : Ref Ctxt Defs} ->
                  {auto s : Ref Syn SyntaxInfo} ->
                  PTerm -> Core (List String)
getDocsForPTerm (PRef fc name) = getDocsForName fc name
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
                        [(_, doc)] => case lines doc of
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
