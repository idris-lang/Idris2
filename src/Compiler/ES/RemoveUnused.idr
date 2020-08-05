module Compiler.ES.RemoveUnused

import Data.SortedSet
import Data.SortedMap
import Data.Vect
import Data.List

import Core.CompileExpr
import Core.Name
import Core.FC

import Debug.Trace

mutual
  usedNames : NamedCExp -> SortedSet Name
  usedNames (NmLocal fc n) = empty
  usedNames (NmRef fc n) = insert n empty
  usedNames (NmLam fc n e) = usedNames e
  usedNames (NmApp fc x args) = usedNames x `union` concat (usedNames <$> args)
  usedNames (NmPrimVal fc c) = empty
  usedNames (NmOp fc op args) = concat $ usedNames <$> args
  usedNames (NmConCase fc sc alts def) = (usedNames sc `union` concat (usedNamesConAlt <$> alts)) `union` maybe empty usedNames def
  usedNames (NmConstCase fc sc alts def) = (usedNames sc `union` concat (usedNamesConstAlt <$> alts)) `union` maybe empty usedNames def
  usedNames (NmExtPrim fc p args) = concat $ usedNames <$> args
  usedNames (NmCon fc x t args) = concat $ usedNames <$> args
  usedNames (NmDelay fc t) = usedNames t
  usedNames (NmForce fc t) = usedNames t
  usedNames (NmLet fc x val sc) = usedNames val `union` usedNames sc
  usedNames (NmErased fc) = empty
  usedNames (NmCrash fc msg) = empty

  usedNamesConAlt : NamedConAlt -> SortedSet Name
  usedNamesConAlt (MkNConAlt n t args exp) = usedNames exp

  usedNamesConstAlt : NamedConstAlt -> SortedSet Name
  usedNamesConstAlt (MkNConstAlt c exp) = usedNames exp

usedNamesDef : NamedDef -> SortedSet Name
usedNamesDef (MkNmFun args exp) = usedNames exp
usedNamesDef (MkNmError exp) = usedNames exp
usedNamesDef (MkNmForeign cs args ret) = empty
usedNamesDef (MkNmCon _ _ _) = empty

defsToUsedMap : List (Name, FC, NamedDef) -> SortedMap Name (SortedSet Name)
defsToUsedMap defs =
  fromList $ (\(n,_,d)=> (n, usedNamesDef d)) <$> defs

calcUsed : SortedSet Name -> SortedMap Name (SortedSet Name) -> List Name -> SortedSet Name
calcUsed done d [] = done
calcUsed done d xs =
  let used_in_xs = foldl f empty $ (\z => lookup z d) <$> xs
      new_done   = union done (fromList xs)
  in calcUsed (new_done) d (SortedSet.toList $ difference used_in_xs new_done)
  where
    f : SortedSet Name -> Maybe (SortedSet Name) -> SortedSet Name
    f x Nothing = x
    f x (Just y) = union x y

calcUsedDefs : List Name -> List (Name, FC, NamedDef) -> List (Name, FC, NamedDef)
calcUsedDefs names defs =
  let usedNames = calcUsed empty (defsToUsedMap defs) names
  in List.filter (\(n, fc, d) => contains n usedNames) defs

export
defsUsedByNamedCExp : NamedCExp -> List (Name, FC, NamedDef) -> List (Name, FC, NamedDef)
defsUsedByNamedCExp exp defs = calcUsedDefs (SortedSet.toList $ usedNames exp) defs
