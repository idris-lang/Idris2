||| This module provides a simple common subexpression elimination (CSE)
||| algorithm. The main goal right now is to move duplicate
||| expressions introduced during autosearch (which includes
||| interface resolution) to the top level.
|||
||| As such, the functionality provided by this module should
||| be considered a form of whole program optimization.
||| To keep things simple, it operates only on closed terms right
||| now, which are - in case of several occurences - introduced
||| as new zero-argument toplevel functions.
|||
||| The procedure is very simple: In an analysis step, we
||| iterate over all toplevel definitions once, trying to
||| convert every subexpression to a closed one (no free
||| variables). Closed terms are then stored in a `SortedMap`
||| together with their size and count.
|||
||| This map is then pruned: Expressions with a count of 1 are removed,
||| as are very small terms (some experiments showed, that a
||| cut-off size of 5 is a good heuristic). The remaining duplicate
||| expressions are then introduced as new zero-argument toplevel
||| functions and replaced accordingly in all function definitions
||| (including larger extracted subexpressions, if any).
module Compiler.Opts.CSE

import Core.CompileExpr
import Core.Context
import Core.Context.Log
import Core.Name
import Core.TT

import Core.Ord
import Data.List
import Data.Nat
import Data.String
import Data.Vect
import Libraries.Data.SortedMap
import Libraries.Data.NameMap

||| Maping from a pairing of closed terms together with
||| their size (for efficiency) to the number of
||| occurences in toplevel definitions.
public export
UsageMap : Type
UsageMap = SortedMap (Integer, CExp []) (Name, Integer)

--------------------------------------------------------------------------------
--          Size of Expressions
--------------------------------------------------------------------------------

mutual
  -- comparison for `Nat` is (or used to be?) O(n),
  -- therefore, we use `Integer`
  size : CExp ns -> Integer
  size (CLocal _ _)         = 1
  size (CRef _ _)           = 1
  size (CLam _ _ y)         = size y + 1
  size (CLet _ _ _ y z)     = size y + size z + 1
  size (CApp _ _ xs)        = sum (map size xs) + 1
  size (CCon _ _ _ _ xs)    = sum (map size xs) + 1
  size (COp _ _ xs)         = sum (map size xs) + 1
  size (CExtPrim _ _ xs)    = sum (map size xs) + 1
  size (CForce _ _ y)       = size y + 1
  size (CDelay _ _ y)       = size y + 1
  size (CPrimVal _ _)       = 1
  size (CErased _)          = 1
  size (CCrash _ _)         = 1
  size (CConCase _ sc xs x) =
    size sc + sum (map sizeConAlt xs) + sum (map size x) + 1

  size (CConstCase _ sc xs x) =
    size sc + sum (map sizeConstAlt xs) + sum (map size x) + 1

  sizeConAlt : CConAlt ns -> Integer
  sizeConAlt (MkConAlt _ _ _ _ z) = 1 + size z

  sizeConstAlt : CConstAlt ns -> Integer
  sizeConstAlt (MkConstAlt _ y) = 1 + size y

--------------------------------------------------------------------------------
--          State
--------------------------------------------------------------------------------

data Sts : Type where

record St where
  constructor MkSt
  map : UsageMap
  idx : Int

-- adds a new closed expression to the `UsageMap`
-- returning the actual count of occurences.
-- very small expressions are being ignored.
store : Ref Sts St => CExp [] -> Core Integer
store exp =
  let sz = size exp
   in if sz < 5
         then pure 0
         else do
           (MkSt map idx)    <- get Sts

           (name,count,idx2) <-
             case lookup (sz,exp) map of
               Just (nm,cnt) => pure (nm, cnt+1, idx)
               Nothing       => pure (MN "csegen" idx, 1, idx + 1)

           put Sts $ MkSt (insert (sz,exp) (name, count) map) idx2
           pure count

--------------------------------------------------------------------------------
--          Strengthening of Expressions
--------------------------------------------------------------------------------

dropVar :  (pre : List Name)
        -> (n : Nat)
        -> (0 p : IsVar x n (pre ++ ns))
        -> Maybe (IsVar x n pre)
dropVar [] _ _        = Nothing
dropVar (y :: xs) 0 First = Just First
dropVar (y :: xs) (S k) (Later p) =
  case dropVar xs k p of
    Just p' => Just $ Later p'
    Nothing => Nothing

mutual
  -- tries to 'strengthen' an expression by removing
  -- a prefix of bound variables. typically, this is invoked
  -- with `{pre = []}`.
  dropEnv : {pre : List Name} -> CExp (pre ++ ns) -> Maybe (CExp pre)
  dropEnv (CLocal {idx} fc p) = (\q => CLocal fc q) <$> dropVar pre idx p
  dropEnv (CRef fc x) = Just (CRef fc x)
  dropEnv (CLam fc x y) = CLam fc x <$> dropEnv y
  dropEnv (CLet fc x inlineOK y z) =
    CLet fc x inlineOK <$> dropEnv y <*> dropEnv z
  dropEnv (CApp fc x xs) = CApp fc <$> dropEnv x <*> traverse dropEnv xs
  dropEnv (CCon fc x y tag xs) = CCon fc x y tag <$> traverse dropEnv xs
  dropEnv (COp fc x xs) = COp fc x <$> traverse dropEnv xs
  dropEnv (CExtPrim fc p xs) = CExtPrim fc p <$> traverse dropEnv xs
  dropEnv (CForce fc x y) = CForce fc x <$> dropEnv y
  dropEnv (CDelay fc x y) = CDelay fc x <$> dropEnv y
  dropEnv (CConCase fc sc xs x) =
    CConCase fc            <$>
    dropEnv sc             <*>
    traverse dropConAlt xs <*>
    traverse dropEnv x

  dropEnv (CConstCase fc sc xs x) =
    CConstCase fc            <$>
    dropEnv sc               <*>
    traverse dropConstAlt xs <*>
    traverse dropEnv x

  dropEnv (CPrimVal fc x) = Just $ CPrimVal fc x
  dropEnv (CErased fc) = Just $ CErased fc
  dropEnv (CCrash fc x) = Just $ CCrash fc x

  dropConAlt :  {pre : List Name}
             -> CConAlt (pre ++ ns)
             -> Maybe (CConAlt pre)
  dropConAlt (MkConAlt x y tag args z) =
    MkConAlt x y tag args . embed <$> dropEnv z

  dropConstAlt :  {pre : List Name}
               -> CConstAlt (pre ++ ns)
               -> Maybe (CConstAlt pre)
  dropConstAlt (MkConstAlt x y) = MkConstAlt x <$> dropEnv y

--------------------------------------------------------------------------------
--          Analysis
--------------------------------------------------------------------------------

mutual
  -- Tries to convert an expression to a closed term (`CExp []`).
  -- If this is successful, the expression's number of occurences
  -- is increased by one, otherwise, its subexpressions are analyzed
  -- in a similar manner.
  --
  -- We have to be careful here not to count subexpressions too
  -- often. For instance, consider a case of `outerExp (innerExp)`,
  -- where both `outerExp` and `innerExp` are closed terms. `innerExp`
  -- should be added to the set of extracted subexpressions, if
  -- and only if it appears somewhere else in the code,
  -- unrelated to `outerExp`. We must
  -- therefore make sure to analyze subexpressions of closed terms
  -- exactly once for each closed term, otherwise they might
  -- be counted as additional common subexpressions although they are not.
  export
  analyze : Ref Sts St => CExp ns -> Core ()

  -- We ignore prim ops here, since moving them to the toplevel
  -- might interfere with other optimizations, for instance
  -- the one dealing with #1320.
  -- Some other terms are ignored, as I (@stefan-hoeck)
  -- am being conservative here,
  -- not daring to inadvertently change the semantics
  -- of the program.
  analyze c@(COp _ _ _)      = analyzeSubExp c
  analyze c@(CExtPrim _ _ _) = analyzeSubExp c
  analyze c@(CForce _ _ _)   = analyzeSubExp c
  analyze c@(CDelay _ _ _)   = analyzeSubExp c

  analyze exp = case dropEnv {pre = []} exp of
    Just e0 => do
      count <- store e0
      -- only analyze subexpressions of closed terms once
      when (count == 1) $ analyzeSubExp exp
    Nothing => analyzeSubExp exp

  analyzeSubExp : Ref Sts St => CExp ns -> Core ()
  analyzeSubExp (CLocal _ _)         = pure ()
  analyzeSubExp (CRef _ _)           = pure ()
  analyzeSubExp (CLam _ _ y)         = analyze y
  analyzeSubExp (CLet _ _ _ y z)     = analyze y >> analyze z
  analyzeSubExp (CApp fc x xs)       = analyze x >> traverse_ analyze xs
  analyzeSubExp (CCon _ _ _ _ [])    = pure ()
  analyzeSubExp (CCon _ _ _ _ xs)    = traverse_ analyze xs
  analyzeSubExp (COp _ _ xs)         = ignore $ traverseVect analyze xs
  analyzeSubExp (CExtPrim _ _ xs)    = traverse_ analyze xs
  analyzeSubExp (CForce _ _ y)       = analyze y
  analyzeSubExp (CDelay _ _ y)       = analyze y
  analyzeSubExp (CConCase _ sc xs x) =
    analyze sc                     >>
    traverse_ analyzeConAlt xs     >>
    ignore (traverseOpt analyze x)

  analyzeSubExp (CConstCase _ sc xs x) =
    analyze sc                     >>
    traverse_ analyzeConstAlt xs   >>
    ignore (traverseOpt analyze x)

  analyzeSubExp (CPrimVal _ _) = pure ()
  analyzeSubExp (CErased _)    = pure ()
  analyzeSubExp (CCrash _ _)   = pure ()

  analyzeConAlt : { auto c : Ref Sts St } -> CConAlt ns -> Core ()
  analyzeConAlt (MkConAlt _ _ _ _ z) = analyze z

  analyzeConstAlt : Ref Sts St => CConstAlt ns -> Core ()
  analyzeConstAlt (MkConstAlt _ y) = analyze y

analyzeDef : Ref Sts St => CDef -> Core ()
analyzeDef (MkFun args x)    = analyze x
analyzeDef (MkCon _ _ _)     = pure ()
analyzeDef (MkForeign _ _ _) = pure ()
analyzeDef (MkError _)       = pure ()

analyzeName : Ref Sts St => Ref Ctxt Defs => Name -> Core ()
analyzeName fn = do
    defs <- get Ctxt
    Just def <- lookupCtxtExact fn (gamma defs)
        | Nothing => pure ()
    let Just cexp = compexpr def
        | Nothing => pure ()
    analyzeDef cexp

||| Generates a `UsageMap` (a mapping from closed terms
||| to their number of occurences plus newly generated
||| name in case they will be lifted to the toplevel)
export
analyzeNames :  Ref Ctxt Defs => List Name -> Core UsageMap
analyzeNames cns = do
  log "compiler.cse" 10 $ "Analysing " ++ show (length cns) ++ " names"
  s <- newRef Sts $ MkSt empty 0
  traverse_ analyzeName cns
  MkSt res _ <- get Sts
  let filtered = reverse
               . sortBy (comparing $ snd . snd)
               . filter ((> 1) . snd . snd)
               $ SortedMap.toList res

  log "compiler.cse" 10 $ unlines $
    "Selected the following definitions:"
    ::  map (\((sz,_),(name,cnt)) =>
                  show name ++
                  ": count " ++ show cnt ++
                  ", size " ++ show sz
           ) filtered

  pure $ fromList filtered

--------------------------------------------------------------------------------
--          Adjusting Expressions
--------------------------------------------------------------------------------

mutual
  export
  adjust : UsageMap -> CExp ns -> CExp ns
  adjust um exp = case dropEnv {pre = []} exp of
    Nothing => adjustSubExp um exp
    Just e0 => case lookup (size e0, e0) um of
      Just (nm,_) => CApp EmptyFC (CRef EmptyFC nm) []
      Nothing     => adjustSubExp um exp

  adjustSubExp : UsageMap -> CExp ns -> CExp ns
  adjustSubExp um e@(CLocal _ _) = e
  adjustSubExp um e@(CRef _ _) = e
  adjustSubExp um e@(CPrimVal _ _) = e
  adjustSubExp um e@(CErased _) = e
  adjustSubExp um e@(CCrash _ _) = e
  adjustSubExp um (CLam fc x y) = CLam fc x $ adjust um y
  adjustSubExp um (CLet fc x inlineOK y z) =
    CLet fc x inlineOK (adjust um y) (adjust um z)

  adjustSubExp um (CApp fc x xs) =
    CApp fc (adjust um x) (map (adjust um) xs)

  adjustSubExp um (CCon fc x y tag xs) =
    CCon fc x y tag $ map (adjust um) xs

  adjustSubExp um (COp fc x xs) = COp fc x $ map (adjust um) xs

  adjustSubExp um (CExtPrim fc p xs) = CExtPrim fc p $ map (adjust um) xs

  adjustSubExp um (CForce fc x y) = CForce fc x $ adjust um y

  adjustSubExp um (CDelay fc x y) = CDelay fc x $ adjust um y

  adjustSubExp um (CConCase fc sc xs x) =
    CConCase fc (adjust um sc) (map (adjustConAlt um) xs) (map (adjust um) x)

  adjustSubExp um (CConstCase fc sc xs x) =
    CConstCase fc (adjust um sc) (map (adjustConstAlt um) xs) (map (adjust um) x)

  adjustConAlt : UsageMap -> CConAlt ns -> CConAlt ns
  adjustConAlt um (MkConAlt x y tag args z) =
    MkConAlt x y tag args $ adjust um z

  adjustConstAlt : UsageMap -> CConstAlt ns -> CConstAlt ns
  adjustConstAlt um (MkConstAlt x y) = MkConstAlt x $ adjust um y

||| Converts occurences of common subexpressions in toplevel
||| definitions to invocations of the corresponding
||| (newly introduced) zero-argument toplevel functions.
export
adjustDef : UsageMap -> CDef -> CDef
adjustDef um (MkFun args x)      = MkFun args $ adjust um x
adjustDef um d@(MkCon _ _ _)     = d
adjustDef um d@(MkForeign _ _ _) = d
adjustDef um d@(MkError _)       = d

export
cseDef :  {auto c : Ref Ctxt Defs}
       -> UsageMap
       -> Name
       -> Core (Maybe (Name, FC, CDef))
cseDef um n = do
  defs <- get Ctxt
  Just def <- lookupCtxtExact n (gamma defs) | Nothing => pure Nothing
  let Just cexpr =  compexpr def             | Nothing => pure Nothing
  pure $ Just (n, location def, adjustDef um cexpr)

export
cseNewToplevelDefs : UsageMap -> List (Name, FC, CDef)
cseNewToplevelDefs um = map toDef $ SortedMap.toList um
  where toDef : ((Integer, CExp[]),(Name,Integer)) -> (Name, FC, CDef)
        toDef ((_,exp),(nm,_)) =
          (nm, EmptyFC, MkFun [] $ adjustSubExp um exp)
