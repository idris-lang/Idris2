module Compiler.Mutate

import Core.CompileExpr
import Core.Context
import Core.Core
import Core.FC
import Core.Name

import Data.List

%hide Prelude.traverse

updateTag : (Int -> Int) -> (CConAlt vars) -> (CConAlt vars)
updateTag update (MkConAlt nm tag args rhs) = MkConAlt nm (update <$> tag) args rhs

interleave : List a -> List a -> List a
interleave [] ys = ys
interleave (x :: xs) ys = x :: (interleave2 xs ys)
  where
    interleave2 : List a -> List a -> List a
    interleave2 xs (y :: ys) = y :: (interleave xs ys)
    interleave2 xs [] = xs

mutual
  export
  mkMutating : {auto c : Ref Ctxt Defs} -> {vars : _} -> Name -> (tag : Maybe Int) -> CExp vars -> Core (CExp vars)
  mkMutating nm tag (CLam fc x body) =
    let mutating = (mkMutating nm tag body) in
        pure $ CLam fc x !mutating
  mkMutating nm tag (CLet fc n i rhs body) =
    let rhs' = mkMutating nm tag rhs
        body' = mkMutating nm tag body in
        pure $ CLet fc n i !rhs' !body'
  mkMutating nm tag (CApp fc fn args) = pure $ CApp fc !(mkMutating nm tag fn) !(traverse (mkMutating nm tag) args)
  -- if the constructor matches name and tag, replace it by mut, otherwise do nothing
  mkMutating nm tag con@(CCon fc nm' tag' args)  = do
    coreLift $ putStrLn $ "found CCon " ++ show con
    coreLift $ putStrLn $ "replace if match " ++ show nm ++ ":" ++ show tag
    if nm == nm' && tag == tag'
       then do coreLift $ putStrLn "names match, creating additional case"
               pure $ CMut fc nm args
       else do coreLift $ putStrLn "names do not match" ; pure con
  mkMutating nm tag (COp fc aty args) = pure $ COp fc aty !(traverseVect (mkMutating nm tag) args)
  mkMutating nm tag (CExtPrim fc n args) = pure $ CExtPrim fc n !(traverse (mkMutating nm tag) args)
  mkMutating nm tag (CForce fc body) = CForce fc <$> (mkMutating nm tag body)
  mkMutating nm tag (CDelay fc body) = CDelay fc <$> (mkMutating nm tag body)

  -- when we see a CConCase we need to expand it to allow mutating cases and then we
  -- modify each new case to allow the additional mutation from the enclosing scope
  -- this makes a redundant tree traversal, maybe we should do everything in 1 go
  mkMutating nm tag (CConCase fc sc clauses wc) = do
        -- add the mutating clauses for the current
        coreLift $ putStrLn $ "found ConCase with name " ++ show nm ++ ":" ++ show tag
        newClauses <- traverse mutateCaseAlt clauses
        -- The new clauses need to have their tag updated. All non-mutating clauses
        -- are Multiplied by 2 and all _mutating_ ones are * 2 + 1
        -- this allows us to create new tags without requiring any type information
        let clauses' = map (updateTag (*2)) clauses
        let mutatingClauses = map (updateTag (\t => t * 2 + 1)) newClauses
        let allClauses = interleave clauses' mutatingClauses
        pure $ CConCase fc sc !(traverse mutateClause allClauses) wc
    where
      -- mutate the clause but this time replace all `nm` and `tag` since nm' and tag'
      -- have already been added in the lines above
      mutateClause : CConAlt vars -> Core (CConAlt vars)
      mutateClause (MkConAlt nm' tag' args rhs) =
        pure $ MkConAlt nm' tag' args !(mkMutating nm tag rhs)
  mkMutating nm tag (CConstCase fc sc clauses wc) =
    let newClauses = traverse mapClauses clauses in
        pure $ CConstCase fc sc !newClauses wc
    where
      mapClauses : CConstAlt vars -> Core (CConstAlt vars)
      mapClauses (MkConstAlt c rhs) = pure $ MkConstAlt c !(mkMutating nm tag rhs)
  mkMutating nm tag other@(CCrash _ _) =
    do coreLift $ putStrLn ("found crash " ++ show other ++ ", ignoring"); pure other
  mkMutating nm tag other@(CErased _) =
    do coreLift $ putStrLn ("found erased " ++ show other ++ ", ignoring"); pure other
  mkMutating nm tag other@(CPrimVal _ _) =
    do coreLift $ putStrLn ("found primVal " ++ show other ++ ", ignoring"); pure other
  mkMutating nm tag other@(CLocal _ _) =
    do coreLift $ putStrLn ("found local " ++ show other ++ ", ignoring"); pure other
  mkMutating nm tag other@(CRef fc n) = do
    pure other
  mkMutating nm tag other@(CMut _ _ _) =
    do coreLift $ putStrLn ("found mut " ++ show other ++ ", ignoring"); pure other

  ||| Given a name/tag for a constructor, replace all occurences of constructing that value
  ||| on the rhs of a case alternatuve.
  mutateCaseAlt : {auto c : Ref Ctxt Defs} -> {vars : _} -> CConAlt vars -> Core (CConAlt vars)
  mutateCaseAlt (MkConAlt nm tag args rhs) = MkConAlt nm tag args <$> (mkMutating nm tag rhs)

export
addMutatingCases : {auto c : Ref Ctxt Defs} -> Name -> Core ()
addMutatingCases n = do
  defs <- get Ctxt
  Just def <- lookupCtxtExact n (gamma defs)  | _ => pure ()
  let Just (MkFun fargs body) = compexpr def | _ => pure ()
  setCompiled n (MkFun fargs !(mkMutating (UN "") Nothing body))

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
export
expandCases : {vars : List Name} -> {auto c : Ref Ctxt Defs} ->
              CExp vars -> Core (CExp vars)
-- expandCases (CLam fc nm body) = (expandCases body)
-- expandCases (CLet fc nm i rhs body) =
--   do expandCases rhs
--      expandCases body
-- expandCases (CApp fc fn args) = do (expandCases fn) ; (traverse_ expandCases args)
-- expandCases (CCon fc nm tag args) = (traverse_ expandCases args)
-- expandCases (COp fc aty args) = map (const ()) (traverseVect expandCases args)
-- expandCases (CExtPrim fc nm args) = (traverse_ expandCases args)
-- expandCases (CForce fc expr) = (expandCases expr)
-- expandCases (CDelay fc expr) = (expandCases expr)
-- expandCases (CConCase fc sc clauses wc) =
--   traverse_ (\(MkConAlt _ _ _ rhs) => expandCases rhs) clauses
-- expandCases (CConstCase fc sc clauses wc) =
--   traverse_ (\(MkConstAlt c exp) => expandCases exp) clauses
-- expandCases other@(CCrash _ _) =
--   do coreLift $ putStrLn ("found crash " ++ show other ++ ", ignoring"); pure ()
-- expandCases other@(CErased _) =
--   do coreLift $ putStrLn ("found erased " ++ show other ++ ", ignoring"); pure ()
-- expandCases other@(CPrimVal _ _) =
--   do coreLift $ putStrLn ("found primVal " ++ show other ++ ", ignoring"); pure ()
-- expandCases other@(CLocal _ _) =
--   do coreLift $ putStrLn ("found local " ++ show other ++ ", ignoring"); pure ()
-- expandCases other@(CRef fc n) = do
--   defs <- get Ctxt
--   Just gdef <- lookupCtxtExact n (gamma defs) | _ => pure ()
--   let Just (MkFun fargs body) = compexpr gdef | _ => pure ()
--   expanded <- mkMutating {vars=fargs} (UN "") Nothing body
--   let newCDef = MkFun fargs expanded
--   setCompiled n newCDef
-- expandCases other@(CMut _ _ _) =
--   do coreLift $ putStrLn ("found mut " ++ show other ++ ", ignoring"); pure ()
