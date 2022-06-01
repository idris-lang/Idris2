module Idris.IDEMode.Holes

import Core.Env
import Core.Context.Log

import Data.String

import Idris.Resugar
import Idris.Syntax
import Idris.Pretty

import Idris.IDEMode.Commands

import Libraries.Data.String.Extra as L

%default covering

public export
record Premise where
  constructor MkHolePremise
  name         : Name
  type         : IPTerm
  multiplicity : RigCount
  isImplicit   : Bool

impBracket : Bool -> String -> String
impBracket False str = str
impBracket True str = "{" ++ str ++ "}"

export covering
Show Holes.Premise where
  show premise =
    " " ++ showCount premise.multiplicity ++ " "
    ++ impBracket premise.isImplicit (show premise.name ++ " : " ++ show premise.type)

prettyImpBracket : Bool -> Doc ann -> Doc ann
prettyImpBracket False = id
prettyImpBracket True = braces

export
prettyRigHole : RigCount -> Doc IdrisSyntax
prettyRigHole = elimSemi (keyword (pretty0 '0') <+> space)
                         (keyword (pretty0 '1') <+> space)
                         (const $ space <+> space)

export
Pretty IdrisSyntax Holes.Premise where
  pretty premise =
     prettyRigHole premise.multiplicity
     <+> prettyImpBracket premise.isImplicit (pretty0 premise.name <++> colon <++> pretty premise.type)

public export
record Data where
  constructor MkHoleData
  name : Name
  type : IPTerm
  context : List Holes.Premise

export
prettyHoles : List Holes.Data -> Doc IdrisSyntax
prettyHoles holes = case holes of
  []  => "No holes"
  [x] => "1 hole" <+> colon <++> prettyHole x
  xs  => vcat $ (pretty0 (show $ length xs) <++> "holes" <+> colon)
              :: map (indent 2 . prettyHole) xs

  where

   prettyHole : Holes.Data -> Doc IdrisSyntax
   prettyHole x = pretty0 x.name <++> colon <++> pretty x.type


||| If input is a hole, return number of locals in scope at binding
||| point
export
isHole : GlobalDef -> Maybe Nat
isHole def
    = case definition def of
           Hole locs _ => Just locs
           PMDef pi _ _ _ _ =>
                 case holeInfo pi of
                      NotHole => Nothing
                      SolvedHole n => Just n
           None => Just 0
           _ => Nothing


-- Bring these back into REPL.idr
showName : Name -> Bool
showName (UN Underscore) = False
showName (MN _ _) = False
showName _ = True

export
extractHoleData : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          Defs -> Env Term vars -> Name -> Nat -> Term vars ->
          Core Holes.Data
extractHoleData defs env fn (S args) (Bind fc x (Let _ c val ty) sc)
  = extractHoleData defs env fn args (subst val sc)
extractHoleData defs env fn (S args) (Bind fc x b sc)
  = do rest <- extractHoleData defs (b :: env) fn args sc
       let True = showName x
         | False => do log "ide-mode.hole" 10 $ "Not showing name: " ++ show x
                       pure rest
       log "ide-mode.hole" 10 $ "Showing name: " ++ show x
       ity <- resugar env !(normalise defs env (binderType b))
       let premise = MkHolePremise x ity (multiplicity b) (isImplicit b)
       pure $ { context $= (premise ::)  } rest
extractHoleData defs env fn args ty
  = do nty <- normalise defs env ty
       ity <- resugar env nty
       log "ide-mode.hole" 20 $
          "Return type: " ++ show !(toFullNames ty)
          ++ "\n  Evaluated to: " ++ show !(toFullNames nty)
          ++ "\n  Resugared to: " ++ show ity
       pure $ MkHoleData fn ity []


export
holeData : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           Defs -> Env Term vars -> Name -> Nat -> Term vars ->
           Core Holes.Data

holeData gam env fn args ty
  = do hdata <- extractHoleData gam env fn args ty
       pp <- getPPrint
       pure $ if showImplicits pp
              then hdata
              else { context $= dropShadows } hdata
  where
    dropShadows : List Holes.Premise -> List Holes.Premise
    dropShadows [] = []
    dropShadows (premise :: rest)
        = if premise.name `elem` map name rest
             then            dropShadows rest
             else premise :: dropShadows rest

export
getUserHolesData :
  {auto c : Ref Ctxt Defs} ->
  {auto s : Ref Syn SyntaxInfo} ->
  Core (List Holes.Data)
getUserHolesData
    = do defs <- get Ctxt
         let ctxt = gamma defs
         ms  <- getUserHoles
         let globs = concat !(traverse (\n => lookupCtxtName n ctxt) ms)
         let holesWithArgs = mapMaybe (\(n, i, gdef) => do args <- isHole gdef
                                                           pure (n, gdef, args))
                                      globs
         traverse (\n_gdef_args =>
                     -- Inference can't deal with this for now :/
                     let (n, gdef, args) = the (Name, GlobalDef, Nat) n_gdef_args in
                     holeData defs [] n args (type gdef))
                  holesWithArgs

export
showHole : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          Defs -> Env Term vars -> Name -> Nat -> Term vars ->
          Core String

showHole defs env fn args ty
    = do hdata <- holeData defs env fn args ty
         case hdata.context of
           [] => pure $ show (hdata.name) ++ " : " ++ show hdata.type
           _  => pure $
              unlines (map show hdata.context)
              ++ "-------------------------------------\n"
              ++ nameRoot (hdata.name) ++ " : " ++ show hdata.type

export
prettyHole : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             Defs -> Env Term vars -> Name -> Nat -> Term vars ->
             Core (Doc IdrisSyntax)
prettyHole defs env fn args ty
  = do hdata <- holeData defs env fn args ty
       case hdata.context of
         [] => pure $ pretty0 hdata.name <++> colon <++> pretty hdata.type
         _  => pure $ indent 1 (vsep $ map pretty hdata.context) <+> hardline
                  <+> (pretty0 $ replicate 30 '-') <+> hardline
                  <+> pretty0 (nameRoot $ hdata.name) <++> colon <++> pretty hdata.type


premiseIDE : Holes.Premise -> HolePremise
premiseIDE premise = IDE.MkHolePremise
  { name = " " ++ showCount premise.multiplicity ++ " "
               ++ (impBracket premise.isImplicit $
                  show premise.name)
  , type = show premise.type
  }

export
holeIDE : Holes.Data -> IDE.HoleData
holeIDE hole = IDE.MkHoleData
  { name = show hole.name
  , type = show hole.type
  , context = map premiseIDE hole.context
  }
