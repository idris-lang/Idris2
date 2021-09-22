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

public export
data Count = One | C Integer

||| After common subexpression analysis we get a mapping
||| from `Name`s to the closed expressions they replace.
||| We use this mapping for substituting the names back
||| to the corresponding expressions, iff the expression
||| appears in several places.
public export
ReplaceMap : Type
ReplaceMap = SortedMap Name (CExp [], Count)

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
store : Ref Sts St => Integer -> CExp [] -> Core (Maybe Name)
store sz exp =
  if sz < 5
     then pure Nothing
     else do
       (MkSt map idx)    <- get Sts

       (name,count,idx2) <-
         case lookup (sz,exp) map of
           Just (nm,cnt) => pure (nm, cnt+1, idx)
           Nothing       => pure (MN "csegen" idx, 1, idx + 1)

       put Sts $ MkSt (insert (sz,exp) (name, count) map) idx2
       pure (Just name)

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
  analyze : Ref Sts St => CExp ns -> Core (Integer, CExp ns)

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

  analyze exp = do
    (sze, exp') <- analyzeSubExp exp
    case dropEnv {pre = []} exp' of
      Just e0 => do
        Just nm <- store sze e0
          | Nothing => pure (sze, exp')
        pure (sze, CRef EmptyFC nm)
      Nothing => pure (sze, exp')

  analyzeList : Ref Sts St => List (CExp ns) -> Core (Integer, List (CExp ns))
  analyzeList es = do
    (sizes, exps) <- unzip <$> traverse analyze es
    pure (sum sizes, exps)

  analyzeMaybe : Ref Sts St => Maybe (CExp ns) -> Core (Integer, Maybe (CExp ns))
  analyzeMaybe Nothing  = pure (0, Nothing)
  analyzeMaybe (Just e) = do
    (se,e') <- analyze e
    pure (se, Just e')

  analyzeVect : Ref Sts St => Vect n (CExp ns) -> Core (Integer, Vect n (CExp ns))
  analyzeVect es = do
    (sizes, exps) <- unzip <$> traverseVect analyze es
    pure (sum sizes, exps)


  analyzeSubExp : Ref Sts St => CExp ns -> Core (Integer, CExp ns)
  analyzeSubExp e@(CLocal _ _)         = pure (1, e)
  analyzeSubExp e@(CRef _ _)           = pure (1, e)
  analyzeSubExp (CLam f n y)  = do
    (sy, y') <- analyze y
    pure (sy + 1, CLam f n y')
  
  analyzeSubExp (CLet f n i y z) = do
    (sy, y') <- analyze y
    (sz, z') <- analyze z
    pure (sy + sz + 1, CLet f n i y' z')

  analyzeSubExp (CApp fc x xs) = do
    (sx, x')   <- analyze x
    (sxs, xs') <- analyzeList xs
    pure (sx + sxs + 1, CApp fc x' xs')

  analyzeSubExp (CCon f n c t xs) = do 
    (sxs, xs') <- analyzeList xs
    pure (sxs + 1, CCon f n c t xs')

  analyzeSubExp (COp f n xs) = do
    (sxs, xs') <- analyzeVect xs
    pure (sxs + 1, COp f n xs')

  analyzeSubExp (CExtPrim f n xs) = do
    (sxs, xs') <- analyzeList xs
    pure (sxs + 1, CExtPrim f n xs')

  analyzeSubExp (CForce f r y) = do
    (sy, y') <- analyze y
    pure (sy + 1, CForce f r y')

  analyzeSubExp (CDelay f r y) = do
    (sy, y') <- analyze y
    pure (sy + 1, CDelay f r y')

  analyzeSubExp (CConCase f sc xs x) = do
    (ssc, sc') <- analyze sc
    (sxs, xs') <- unzip <$> traverse analyzeConAlt xs
    (sx, x')   <- analyzeMaybe x
    pure (ssc + sum sxs + sx + 1, CConCase f sc' xs' x')

  analyzeSubExp (CConstCase f sc xs x) = do
    (ssc, sc') <- analyze sc
    (sxs, xs') <- unzip <$> traverse analyzeConstAlt xs
    (sx, x')   <- analyzeMaybe x
    pure (ssc + sum sxs + sx + 1, CConstCase f sc' xs' x')

  analyzeSubExp c@(CPrimVal _ _) = pure (1, c)
  analyzeSubExp c@(CErased _)    = pure (1, c)
  analyzeSubExp c@(CCrash _ _)   = pure (1, c)

  analyzeConAlt :  { auto c : Ref Sts St }
                -> CConAlt ns
                -> Core (Integer, CConAlt ns)
  analyzeConAlt (MkConAlt n c t as z) = do
    (sz, z') <- analyze z
    pure (sz + 1, MkConAlt n c t as z')

  analyzeConstAlt : Ref Sts St => CConstAlt ns -> Core (Integer, CConstAlt ns)
  analyzeConstAlt (MkConstAlt c y) = do
    (sy, y') <- analyze y
    pure (sy + 1, MkConstAlt c y')

analyzeDef : Ref Sts St => CDef -> Core ()
analyzeDef (MkFun args x)    = ignore $ analyze x
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

--------------------------------------------------------------------------------
--          Adjusting Counts
--------------------------------------------------------------------------------

mutual
  adjCountExp :  Ref Sts UsageMap
              => (parentCount : Integer)
              -> CExp ns
              -> Core ()

  adjCountSubExp :  Ref Sts UsageMap
                 => (parentCount : Integer)
                 -> CExp ns
                 -> Core ()
  adjCountSubExp _ (CLocal _ _) = pure ()
  adjCountSubExp _ (CRef _ _)   = pure ()
  adjCountSubExp pc (CLam _ _ y) = adjCountExp pc y
  adjCountSubExp pc (CLet _ _ _ y z) = adjCountExp pc y >> adjCountExp pc z
  adjCountSubExp pc (CApp _ x xs) =
    adjCountExp pc x >> traverse_ (adjCountExp pc) xs
  adjCountSubExp pc (CCon _ _ _ _ xs) = traverse_ (adjCountExp pc) xs
  adjCountSubExp pc (COp _ _ xs) = ignore $ traverseVect (adjCountExp pc) xs
  adjCountSubExp pc (CExtPrim _ _ xs) = traverse_ (adjCountExp pc) xs
  adjCountSubExp pc (CForce _ _ y) = adjCountExp pc y
  adjCountSubExp pc (CDelay _ _ y) = adjCountExp pc y
  adjCountSubExp pc (CConCase _ sc xs x) =
    adjCountExp pc sc >>
    traverse_ (adjCountConAlt pc) xs >>
    ignore (traverseOpt (adjCountExp pc) x)

  adjCountSubExp pc (CConstCase _ sc xs x) =
    adjCountExp pc sc >>
    traverse_ (adjCountConstAlt pc) xs >>
    ignore (traverseOpt (adjCountExp pc) x)

  adjCountSubExp _ (CPrimVal _ _) = pure ()
  adjCountSubExp _ (CErased _)    = pure ()
  adjCountSubExp _ (CCrash _ _)   = pure ()

  adjCountConAlt :  Ref Sts UsageMap
                 => (parentCount : Integer)
                 -> CConAlt ns
                 -> Core ()
  adjCountConAlt pc (MkConAlt _ _ _ _ z) = adjCountExp pc z

  adjCountConstAlt :  Ref Sts UsageMap
                   => (parentCount : Integer)
                   -> CConstAlt ns
                   -> Core ()
  adjCountConstAlt pc (MkConstAlt _ z) = adjCountExp pc z

adjCounts : UsageMap -> Core UsageMap
adjCounts um = 
  let exps = (\((_,e),(_,c)) => (c,e)) <$> SortedMap.toList um
   in do
    s <- newRef Sts $ um
    traverse_ (uncurry adjCountExp) exps
    get Sts

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
               $ SortedMap.toList res

  log "compiler.cse" 10 $ unlines $
    "Found the following definitions:"
    ::  map (\((sz,_),(name,cnt)) =>
                  show name ++
                  ": count " ++ show cnt ++
                  ", size " ++ show sz
           ) filtered

  adjCounts res

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
-- adjustDef um (MkFun args x)      = MkFun args $ adjust um x
-- adjustDef um d@(MkCon _ _ _)     = d
-- adjustDef um d@(MkForeign _ _ _) = d
-- adjustDef um d@(MkError _)       = d

export
cseDef :  {auto c : Ref Ctxt Defs}
       -> UsageMap
       -> Name
       -> Core (Maybe (Name, FC, CDef))
-- cseDef um n = do
--   defs <- get Ctxt
--   Just def <- lookupCtxtExact n (gamma defs) | Nothing => pure Nothing
--   let Just cexpr =  compexpr def             | Nothing => pure Nothing
--   pure $ Just (n, location def, adjustDef um cexpr)

export
cseNewToplevelDefs : UsageMap -> List (Name, FC, CDef)
-- cseNewToplevelDefs um = map toDef $ SortedMap.toList um
--   where toDef : ((Integer, CExp[]),(Name,Integer)) -> (Name, FC, CDef)
--         toDef ((_,exp),(nm,_)) =
--           (nm, EmptyFC, MkFun [] $ adjustSubExp um exp)
