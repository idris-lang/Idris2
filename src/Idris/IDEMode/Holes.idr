module Idris.IDEMode.Holes

import Core.Env

import Idris.Resugar
import Idris.Syntax

record HolePremise where
  constructor MkHolePremise
  name         : Name
  type         : PTerm
  multiplicity : RigCount  
  isImplicit   : Bool
  

record HoleData where
  constructor MkHoleData
  name : Name
  type : PTerm
  context : List HolePremise

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
           _ => Nothing



-- Bring these back into REPL.idr
showName : Name -> Bool
showName (UN "_") = False
showName (MN _ _) = False
showName _ = True

showCount : RigCount -> String
showCount = elimSemi
                 " 0 "
                 " 1 "
                 (const "   ")

impBracket : Bool -> String -> String
impBracket False str = str
impBracket True str = "{" ++ str ++ "}"

tidy : Name -> String
tidy (MN n _) = n
tidy n = show n

export
extractHoleData : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          Defs -> Env Term vars -> Name -> Nat -> Term vars ->
          Core HoleData
extractHoleData defs env fn (S args) (Bind fc x (Let c val ty) sc) 
  = extractHoleData defs env fn args (subst val sc)
extractHoleData defs env fn (S args) (Bind fc x b sc)
  = do rest <- extractHoleData defs (b :: env) fn args sc
       let True = showName x
         | False => pure rest
       ity <- resugar env !(normalise defs env (binderType b))
       let premise = MkHolePremise x ity (multiplicity b) (implicitBind b)
       pure $ record { context $= (premise ::)  } rest
  where
    implicitBind : Binder (Term vars) -> Bool
    implicitBind (Pi _ Explicit _) = False
    implicitBind (Pi _ _ _) = True
    implicitBind (Lam _ Explicit _) = False
    implicitBind (Lam _ _ _) = True
    implicitBind _ = False
   
extractHoleData defs env fn args ty
  = do ity <- resugar env !(normalise defs env ty)
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
              then record { context $= dropShadows } hdata
              else hdata
  where
    dropShadows : List HolePremise -> List HolePremise
    dropShadows [] = []
    dropShadows (premise :: rest)
        = if premise.name `elem` map name rest
             then            dropShadows rest
             else premise :: dropShadows rest
       

export
showHole : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          Defs -> Env Term vars -> Name -> Nat -> Term vars ->
          Core String
showHole defs env fn args ty
    = do hdata <- holeData defs env fn args ty
         pure $ concat 
              (map (\hole => showCount hole.multiplicity
                             ++ (impBracket hole.isImplicit $
                                 tidy hole.name ++ " : " ++ (show hole.type) ++ "\n" )
                   ) hdata.context)
              ++ "-------------------------------------\n"
              ++ nameRoot (hdata.name) ++ " : " ++ show hdata.type


