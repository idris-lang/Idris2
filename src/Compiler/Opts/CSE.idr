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
||| together with their size and count. In order to only use
||| linear space w.r.t. term size, we start this analysis at the
||| leaves and substitute closed terms with the machine generated
||| names before analyzing parent terms.
|||
||| In a second step, we compare the count of each machine
||| generated name with the count of its parent expression.
||| If they are the same, the name is dropped and replaces with
||| a CSE optimized version of the original expression, otherwise
||| the name is kept and a new zero argumet function of the
||| given name is added to the toplevel, thus eliminating the
||| duplicate expressions.
module Compiler.Opts.CSE

import Core.CompileExpr
import Core.Context
import Core.Context.Log
import Core.Name
import Core.TT

import Core.Ord
import Data.List
import Data.String
import Data.Vect
import Libraries.Data.SortedMap

||| Maping from a pairing of closed terms together with
||| their size (for efficiency) to the number of
||| occurences in toplevel definitions.
public export
UsageMap : Type
UsageMap = SortedMap (Integer, CExp []) (Name, Integer)

||| Number of appearances of a closed expression.
|||
|||  `Once` : The expression occurs exactly once.
|||  `Many` : The expression occurs more than once.
|||  `C n`  : The expression has been counted `n` times
|||           but we will have to compare this value
|||           with the number of occurences of its parent
|||           expression to decide whether it occured
|||           only once or several times.
|||
public export
data Count = Once | Many | C Integer

Show Count where
  show Once  = "Once"
  show Many  = "Many"
  show (C n) = "C " ++ show n

||| After common subexpression analysis we get a mapping
||| from `Name`s to the closed expressions they replace.
||| We use this mapping for substituting the names back
||| to the corresponding expressions, if and only if
||| the expression appears only in one place.
public export
ReplaceMap : Type
ReplaceMap = SortedMap Name (CExp [], Count)

toReplaceMap : UsageMap -> ReplaceMap
toReplaceMap = SortedMap.fromList
             . map (\((_,exp),(n,c)) => (n, (exp, C c)))
             . SortedMap.toList

--------------------------------------------------------------------------------
--          State
--------------------------------------------------------------------------------

data Sts : Type where

record St where
  constructor MkSt
  map : UsageMap
  idx : Int

-- Adds a new closed expression to the `UsageMap`
-- returning a new machine generated name to be used
-- if the expression should be lifted to the toplevel.
-- Very small expressions are being ignored.
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
  -- Tries to convert an expression and its
  -- sub-expression to closed terms (`CExp []`).
  -- Every occurence of a closed term will be replaced by
  -- a machine generated name and its count in the `UsageMap`
  -- will be increased by one.
  --
  -- Because we start at the leafs and substitute all closed
  -- expressions with machine generated names, we have to
  -- keep track of the original expression's size, which
  -- is returned in addition to the adjusted expressions.
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

analyzeDef : Ref Sts St => CDef -> Core CDef
analyzeDef (MkFun args x)      = MkFun args . snd <$> analyze x
analyzeDef d@(MkCon _ _ _)     = pure d
analyzeDef d@(MkForeign _ _ _) = pure d
analyzeDef d@(MkError _)       = pure d

analyzeName :  Ref Sts St
            => Ref Ctxt Defs
            => Name
            -> Core (Maybe (Name, FC, CDef))
analyzeName fn = do
    defs <- get Ctxt
    Just def <- lookupCtxtExact fn (gamma defs)
        | Nothing => do log "compile.execute" 50 $ "Couldn't find " ++ show fn
                        pure Nothing
    let Just cexp = compexpr def
        | Nothing => do log "compile.execute" 50 $ "Couldn't compile " ++ show fn
                        pure Nothing
    cexp' <- analyzeDef cexp
    pure $ Just (fn, location def, cexp')

--------------------------------------------------------------------------------
--          Replacing Expressions
--------------------------------------------------------------------------------

mutual
  -- During the analysis step, we replaced every closed
  -- expression with a machine generated name. We only
  -- want to keep these substitutions, if a closed term
  -- appears in several distinct locations in the code.
  --
  -- We therefore check for each machine generated name, if
  -- the corresponding closed term has a count > 1. If that's
  -- not the case, the machine generated name will be dropped
  -- and replaces with the CSE-optimized original term.
  --
  -- However, during the analysis step, we might get counts > 1
  -- for expressions that still are used only once.
  -- Consider the following situation:
  --
  --    fun1 = exp1(exp2(exp3))
  --    fun2 = exp4(exp2(exp3))
  --
  -- In the example above, `exp2` is a proper common subexpression
  -- that should be lifted to the toplevel, but exp3 is not, although
  -- it will also get a count of 2 in the `UsageMap`.
  -- We therefore compare the count of each child expression
  -- with the count of their parent expression, lifting
  -- a child only if it was counted mor often than its parent.
  replaceRef :  Ref ReplaceMap ReplaceMap
             => Ref Ctxt Defs
             => (parentCount : Integer)
             -> FC
             -> Name
             -> Core (CExp ns)
  replaceRef pc fc n = do
    log "compiler.cse" 10 $ "Trying to replace " ++ show n ++ ": "
    res <- lookup n <$> get ReplaceMap
    case res of
      -- not a name generated during CSE
      Nothing          => do
        log "compiler.cse" 10 $ "  not a name generated during CSE"
        pure (CRef fc n)

      -- Expression count has already been checked and occurs
      -- several times. Replace it with the machine generated name.
      Just (exp, Many) => do
        log "compiler.cse" 10 $ "  already replaced: Occurs many times"
        pure (CApp EmptyFC (CRef fc n) [])


      -- Expression count has already been checked and occurs
      -- only once. Substitute the machine generated name with
      -- the original (but CSE optimized) exp
      Just (exp, Once) => do
        log "compiler.cse" 10 $ "  already replaced: Occurs once"
        pure (embed exp)

      -- Expression count has not yet been compared with the
      -- parent count. Do this now.
      Just (exp, C c)  => do
        log "compiler.cse" 10 $  "  expression of unknown quantity ("
                              ++ show c
                              ++ " occurences)"
        -- We first have to replace all child expressions.
        exp' <- replaceExp c exp
        if c > pc
           -- This is a common subexpression. We set its count to `Many`
           -- and replace it with the machine generated name.
           then do
             log "compiler.cse" 10 $ show n ++ " assigned quantity \"Many\""
             update ReplaceMap (insert n (exp', Many))
             pure (CApp EmptyFC (CRef fc n) [])

           -- This expression occurs only once. We set its count to `Once`
           -- and keep it.
           else do
             log "compiler.cse" 10 $ show n ++ " assigned quantity \"Once\""
             update ReplaceMap (insert n (exp', Once))
             pure (embed exp')

  replaceExp :  Ref ReplaceMap ReplaceMap
             => Ref Ctxt Defs
             => (parentCount : Integer)
             -> CExp ns
             -> Core (CExp ns)
  replaceExp _ e@(CLocal _ _)  = pure e
  replaceExp pc (CRef f n)     = replaceRef pc f n
  replaceExp pc (CLam f n y)   = CLam f n <$> replaceExp pc y
  replaceExp pc (CLet f n i y z) =
    CLet f n i <$> replaceExp pc y <*> replaceExp pc z
  replaceExp pc (CApp f x xs) =
    CApp f <$> replaceExp pc x <*> traverse (replaceExp pc) xs
  replaceExp pc (CCon f n c t xs) =
    CCon f n c t <$> traverse (replaceExp pc) xs
  replaceExp pc (COp f n xs) =
    COp f n <$> traverseVect (replaceExp pc) xs
  replaceExp pc (CExtPrim f n xs) =
    CExtPrim f n <$> traverse (replaceExp pc) xs
  replaceExp pc (CForce f r y) =
    CForce f r <$> replaceExp pc y
  replaceExp pc (CDelay f r y) =
    CDelay f r <$> replaceExp pc y
  replaceExp pc (CConCase f sc xs x) =
    CConCase f                     <$>
    replaceExp pc sc               <*>
    traverse (replaceConAlt pc) xs <*>
    traverseOpt (replaceExp pc) x

  replaceExp pc (CConstCase f sc xs x) = do
    CConstCase f                     <$>
    replaceExp pc sc                 <*>
    traverse (replaceConstAlt pc) xs <*>
    traverseOpt (replaceExp pc) x

  replaceExp _ c@(CPrimVal _ _) = pure c
  replaceExp _ c@(CErased _)    = pure c
  replaceExp _ c@(CCrash _ _)   = pure c

  replaceConAlt :  Ref ReplaceMap ReplaceMap
                => Ref Ctxt Defs
                => (parentCount : Integer)
                -> CConAlt ns
                -> Core (CConAlt ns)
  replaceConAlt pc (MkConAlt n c t as z) =
    MkConAlt n c t as <$> replaceExp pc z

  replaceConstAlt :  Ref ReplaceMap ReplaceMap
                  => Ref Ctxt Defs
                  => (parentCount : Integer)
                  -> CConstAlt ns
                  -> Core (CConstAlt ns)
  replaceConstAlt pc (MkConstAlt c y) =
    MkConstAlt c <$> replaceExp pc y

replaceDef :  Ref ReplaceMap ReplaceMap
           => Ref Ctxt Defs
           => (Name, FC, CDef)
           -> Core (Name, FC, CDef)
replaceDef (n, fc, MkFun args x) =
  (\x' => (n, fc, MkFun args x')) <$> replaceExp 1 x
replaceDef (n, fc, d@(MkCon _ _ _))     = pure (n, fc, d)
replaceDef (n, fc, d@(MkForeign _ _ _)) = pure (n, fc, d)
replaceDef (n, fc, d@(MkError _))       = pure (n, fc, d)

newToplevelDefs : ReplaceMap -> List (Name, FC, CDef)
newToplevelDefs rm = mapMaybe toDef $ SortedMap.toList rm
  where toDef : (Name,(CExp[],Count)) -> Maybe (Name, FC, CDef)
        toDef (nm,(exp,Many)) = Just (nm, EmptyFC, MkFun [] exp)
        toDef _               = Nothing

undefinedCount : (Name, (CExp [], Count)) -> Bool
undefinedCount (_, _, Once) = False
undefinedCount (_, _, Many) = False
undefinedCount (_, _, C x)  = True

||| Runs the CSE alorithm on all provided names and
||| the given main expression.
export
cse :  Ref Ctxt Defs
    => (definitionNames : List Name)
    -> (mainExpr        : CExp ns)
    -> Core (List (Name, FC, CDef), CExp ns)
cse defs me = do
  log "compiler.cse" 10 $ "Analysing " ++ show (length defs) ++ " names"
  s            <- newRef Sts $ MkSt empty 0
  analyzedDefs <- catMaybes <$> traverse analyzeName defs
  MkSt um _    <- get Sts
  srep         <- newRef ReplaceMap $ toReplaceMap um
  replacedDefs <- traverse replaceDef analyzedDefs
  replacedMain <- replaceExp 1 me
  replaceMap   <- get ReplaceMap
  let filtered = SortedMap.toList replaceMap
  log "compiler.cse" 10 $ unlines $
    "Found the following unadjusted subexpressions:"
    ::  map (\(name,(_,cnt)) =>
                  show name ++ ": count " ++ show cnt
           ) filtered
  pure (newToplevelDefs replaceMap ++ replacedDefs, replacedMain)
