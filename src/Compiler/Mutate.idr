module Compiler.Mutate

import Core.CompileExpr
import Core.Name

import Data.List

mkMutating : (sc : CExp vars) -> Name -> (tag : Maybe Int) -> CExp (vs ++ vars) -> CExp vars
mkMutating sc nm tag con@(CCon fc nm' tag' args)  =
  if nm == nm' && tag == tag' then CMut fc nm args
                              else con
mkMutating sc nm tag (CLam fc x body) = CLam fc x (mkMutating sc nm tag body)
mkMutating sc nm tag (CLet fc x i body) = CLet fc x i (mkMutating sc nm tag body)
mkMutating sc nm tag (COp fc aty args ) = COp fc ary (map (mkMutating sc nm tag) args)

mutateRhs : (sc : CExp vars) -> CConAlt vars -> CConAlt vars
mutateRhs sc (MkConAlt nm tag args rhs) = MkConAlt nm tag args (mkMutating {vs=[]} sc nm tag rhs)


updateTag : Int -> (CConAlt vars) -> (CConAlt vars)
updateTag offset (MkConAlt nm tag args rhs) = MkConAlt nm ((+ offset) <$> tag) args rhs

||| Duplicate every clause and replace every constructor on the rhs by a mutating version
||| The transformation on takes place for patterns which are not wildcards
||| It only replaces constructors that match the ones we match on
||| The tag for mutating version is simply offest by the amount of matches we have
||| the following tree:
||| case v of
|||      Match1 a => … -- tag 0
|||      Match2 b => … -- tag 1
|||      Match3 c => … -- tag 2
|||
||| will be replaced by:
||| case v of
|||      Match1 a => … -- tag 0
|||      Match2 b => … -- tag 1
|||      Match3 c => … -- tag 2
|||      Match1' a => … -- tag 3 mutating rhs
|||      Match2' b => … -- tag 4 mutating rhs
|||      Match3' c => … -- tag 5 mutating rhs
||| wildcards are not duplicated since they do not match on a known constructor
||| case v of
|||      Match1 a => …
|||      _ => …
||| will be replaced by:
||| case v of
|||      Match1 a => … -- tag 0
|||      Match1' a => … -- tag 1
|||      _ => … -- not duplicated since we do not know which constructor to replace
expandCase : CExp vars -> CExp vars
expandCase (CConCase fc sc clauses wild) =
  let newClauses = map (mutateRhs sc) clauses
      updatedClauses = map (updateTag (cast $ List.length clauses)) newClauses in
      CConCase fc sc (clauses ++ updatedClauses) wild
expandCase exp = exp
