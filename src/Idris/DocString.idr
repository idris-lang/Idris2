module Idris.DocString

import Core.Context
import Core.Core
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

    getConstructorDoc : Name -> Core (Maybe String)
    getConstructorDoc con
        = do defs <- get Ctxt
             Just def <- lookupCtxtExact con (gamma defs)
                  | Nothing => pure Nothing
             syn <- get Syn
             let [(n, str)] = lookupName con (docstrings syn)
                  | _ => pure Nothing
             pure (Just (nameRoot n ++ "\n" ++ indent str))

    -- TODO: If it's an interface, list the methods and implementations?
    getExtra : Name -> GlobalDef -> Core String
    getExtra n d
        = case definition d of
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
    showDoc (n, "") = pure $ "No documentation for " ++ show n
    showDoc (n, str)
        = do let doc = show n ++ "\n" ++ indent str
             defs <- get Ctxt
             def <- lookupCtxtExact n (gamma defs)
             extra <- maybe (pure "") (getExtra n) def
             pure (doc ++ extra)
