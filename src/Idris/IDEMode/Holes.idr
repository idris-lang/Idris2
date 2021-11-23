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
record HolePremise where
  constructor MkHolePremise
  name         : Name
  type         : IPTerm
  multiplicity : RigCount
  isImplicit   : Bool


public export
record HoleData where
  constructor MkHoleData
  name : Name
  type : IPTerm
  context : List HolePremise

export
prettyHoles : List HoleData -> Doc IdrisSyntax
prettyHoles holes = case holes of
  []  => "No holes"
  [x] => "1 hole" <+> colon <++> prettyHole x
  xs  => vcat $ (pretty (length xs) <++> pretty "holes" <+> colon)
              :: map (indent 2 . prettyHole) xs

  where

   prettyHole : HoleData -> Doc IdrisSyntax
   prettyHole x = pretty x.name <++> colon <++> prettyTerm x.type



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

impBracket : Bool -> String -> String
impBracket False str = str
impBracket True str = "{" ++ str ++ "}"

prettyImpBracket : Bool -> Doc ann -> Doc ann
prettyImpBracket False = id
prettyImpBracket True = braces

tidy : Name -> String
tidy (MN n _) = n
tidy n = show n

prettyName : Name -> Doc ann
prettyName (MN n _) = pretty n
prettyName n = pretty n

export
extractHoleData : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          Defs -> Env Term vars -> Name -> Nat -> Term vars ->
          Core HoleData
extractHoleData defs env fn (S args) (Bind fc x (Let _ c val ty) sc)
  = extractHoleData defs env fn args (subst val sc)
extractHoleData defs env fn (S args) (Bind fc x b sc)
  = do rest <- extractHoleData defs (b :: env) fn args sc
       let True = showName x
         | False => do log "idemode.hole" 10 $ "Not showing name: " ++ show x
                       pure rest
       log "idemode.hole" 10 $ "Showing name: " ++ show x
       ity <- resugar env !(normalise defs env (binderType b))
       let premise = MkHolePremise x ity (multiplicity b) (isImplicit b)
       pure $ record { context $= (premise ::)  } rest
extractHoleData defs env fn args ty
  = do nty <- normalise defs env ty
       ity <- resugar env nty
       log "idemode.hole" 20 $
          "Return type: " ++ show !(toFullNames ty)
          ++ "\n  Evaluated to: " ++ show !(toFullNames nty)
          ++ "\n  Resugared to: " ++ show ity
       pure $ MkHoleData fn ity []


export
holeData : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           Defs -> Env Term vars -> Name -> Nat -> Term vars ->
           Core HoleData

holeData gam env fn args ty
  = do hdata <- extractHoleData gam env fn args ty
       pp <- getPPrint
       pure $ if showImplicits pp
              then hdata
              else record { context $= dropShadows } hdata
  where
    dropShadows : List HolePremise -> List HolePremise
    dropShadows [] = []
    dropShadows (premise :: rest)
        = if premise.name `elem` map name rest
             then            dropShadows rest
             else premise :: dropShadows rest

export
getUserHolesData :
  {auto c : Ref Ctxt Defs} ->
  {auto s : Ref Syn SyntaxInfo} ->
  Core (List HoleData)
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
           _  => pure $ concat
              (map (\premise => " " ++ showCount premise.multiplicity ++ " "
                             ++ (impBracket premise.isImplicit $
                                 tidy premise.name ++ " : " ++ (show premise.type) ++ "\n" )
                   ) hdata.context)
              ++ "-------------------------------------\n"
              ++ nameRoot (hdata.name) ++ " : " ++ show hdata.type

export
prettyRigHole : RigCount -> Doc ann
prettyRigHole = elimSemi (pretty '0' <+> space)
                         (pretty '1' <+> space)
                         (const $ space <+> space)

export
prettyHole : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             Defs -> Env Term vars -> Name -> Nat -> Term vars ->
             Core (Doc IdrisSyntax)
prettyHole defs env fn args ty
  = do hdata <- holeData defs env fn args ty
       case hdata.context of
            [] => pure $ pretty hdata.name <++> colon <++> prettyTerm hdata.type
            _  => pure $ (indent 1 $ vsep $
                            map (\premise => prettyRigHole premise.multiplicity
                                    <+> prettyImpBracket premise.isImplicit (prettyName premise.name <++> colon <++> prettyTerm premise.type))
                                    hdata.context) <+> hardline
                    <+> (pretty $ L.replicate 30 '-') <+> hardline
                    <+> pretty (nameRoot $ hdata.name) <++> colon <++> prettyTerm hdata.type

sexpPremise : HolePremise -> SExp
sexpPremise premise =
  SExpList [StringAtom $ " " ++ showCount premise.multiplicity ++ " "
                       ++ (impBracket premise.isImplicit $
                           tidy premise.name)
           ,StringAtom $ show premise.type
           ,SExpList [] -- TODO: metadata
           ]

export
sexpHole : HoleData -> SExp
sexpHole hole = SExpList
  [ StringAtom (show  hole.name)
  , SExpList $ map sexpPremise hole.context  -- Premises
  , SExpList [ StringAtom $ show hole.type   -- Conclusion
             , SExpList[]]    -- TODO: Highlighting information
  ]
