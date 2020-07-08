module Idris.DocString

import Core.Context
import Core.Core
import Core.Env
import Core.TT

import Idris.Resugar
import Idris.Syntax

import Data.ANameMap
import Data.List
import Data.Maybe
import Data.NameMap
import Data.Strings

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
                 List String -> Name -> String ->
                 Core ()
addDocStringNS ns n_in doc
    = do n <- inCurrentNS n_in
         let n' = case n of
                       NS old root => NS (ns ++ old) root
                       root => NS ns root
         syn <- get Syn
         put Syn (record { docstrings $= addName n' doc,
                           saveDocstrings $= insert n' () } syn)

export
getDocsFor : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             FC -> Name -> Core (List String)
getDocsFor fc n
    = do syn <- get Syn
         defs <- get Ctxt
         all@(_ :: _) <- lookupCtxtName n (gamma defs)
             | _ => throw (UndefinedName fc n)
         let ns@(_ :: _) = concatMap (\n => lookupName n (docstrings syn))
                                     (map fst all)
             | [] => pure ["No documentation for " ++ show n]
         traverse showDoc ns
  where
    indent : String -> String
    indent str = unlines $ map ("\t" ++) (lines str)

    showTotal : Name -> Totality -> String
    showTotal n tot
        = "\nTotality: " ++ show tot

    getNameDoc : Name -> Core (Maybe String)
    getNameDoc con
        = do defs <- get Ctxt
             Just def <- lookupCtxtExact con (gamma defs)
                  | Nothing => pure Nothing
             syn <- get Syn
             let [(n, str)] = lookupName con (docstrings syn)
                  | _ => pure Nothing
             ty <- normaliseHoles defs [] (type def)
             pure (Just (nameRoot n ++ " : " ++ show !(resugar [] ty)
                          ++ "\n" ++ indent str))

    getIFaceDoc : (Name, IFaceInfo) -> Core String
    getIFaceDoc (n, iface)
        = do mdocs <- traverse getNameDoc (map fst (methods iface))
             case mapMaybe id mdocs of
                  [] => pure ""
                  docs => pure $ "\nMethods:\n" ++ concat docs

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
                   => do cdocs <- traverse getNameDoc
                                           !(traverse toFullNames cons)
                         case mapMaybe id cdocs of
                              [] => pure ""
                              docs => pure $ "\nConstructors:\n" ++ concat docs
               _ => pure ""

    showDoc : (Name, String) -> Core String
    showDoc (n, str)
        = do defs <- get Ctxt
             Just def <- lookupCtxtExact n (gamma defs)
                  | Nothing => throw (UndefinedName fc n)
             ty <- normaliseHoles defs [] (type def)
             let doc = show n ++ " : " ++ show !(resugar [] ty)
                              ++ "\n" ++ indent str
             extra <- getExtra n def
             pure (doc ++ extra)
