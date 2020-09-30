module Idris.Parser.Let

import Idris.Syntax
import Text.Bounded

import Data.Either
import Data.List1

import Utils.String

%default total

------------------------------------------------------------------------
-- Types

-- `let ... in ...` is used for two different notions:
-- * pattern-matching let binders to locally take an expression apart
-- * Local definitions that can be recursive

public export
record LetBinder where
  constructor MkLetBinder
  letUsage     : RigCount
  letPattern   : PTerm
  letBoundType : PTerm
  letBoundTerm : PTerm
  letUnhappy   : List PClause

public export
LetDecl : Type
LetDecl = List PDecl

------------------------------------------------------------------------
-- Let-binding functions

letFactory : (List (WithBounds LetBinder) -> a -> a) ->
             (WithBounds LetDecl -> a -> a) ->
             List1 (WithBounds (Either LetBinder LetDecl)) ->
             a -> a
letFactory letBind letDeclare blocks scope = foldr mkLet scope groups where

  LetBlock : Type
  LetBlock = Either (List1 (WithBounds LetBinder)) (List1 (WithBounds LetDecl))

  groups : List LetBlock
  groups = compress (forget $ map (\ b => bimap (<$ b) (<$ b) b.val) blocks)

  mkLet : LetBlock -> a -> a
  mkLet (Left  letBinds) = letBind (forget letBinds)
  mkLet (Right letDecls) =
    let bounds = mergeBounds (head letDecls) (last letDecls)
    in letDeclare (concatMap val letDecls <$ bounds)

export
mkLets : FileName ->
         List1 (WithBounds (Either LetBinder LetDecl)) ->
         PTerm -> PTerm
mkLets fname = letFactory buildLets
  (\ decls, scope => PLocal (boundToFC fname decls) decls.val scope)

  where

    buildLets : List (WithBounds LetBinder) -> PTerm -> PTerm
    buildLets [] sc = sc
    buildLets (b :: rest) sc
      = let (MkLetBinder rig pat ty val alts) = b.val
            fc = boundToFC fname b
        in PLet fc rig pat ty val (buildLets rest sc) alts

export
mkDoLets : FileName ->
           List1 (WithBounds (Either LetBinder LetDecl)) ->
           List PDo
mkDoLets fname lets = letFactory
    (\ binds, rest => buildDoLets binds ++ rest)
    (\ decls, rest => DoLetLocal (boundToFC fname decls) decls.val :: rest)
    lets
    []

  where

    buildDoLets : List (WithBounds LetBinder) -> List PDo
    buildDoLets [] = []
    buildDoLets (b :: rest) = let fc = boundToFC fname b in case b.val of
      (MkLetBinder rig (PRef fc' (UN n)) ty val []) =>
         (if lowerFirst n
            then DoLet fc (UN n) rig ty val
            else DoLetPat fc (PRef fc' (UN n)) ty val []
         ) :: buildDoLets rest
      (MkLetBinder rig pat ty val alts) => DoLetPat fc pat ty val alts :: buildDoLets rest
