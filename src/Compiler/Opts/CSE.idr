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
import Core.Context.Log
import Core.Options

import Core.Ord
import Data.String
import Data.SortedMap
import Data.Vect

import Libraries.Data.Erased
import Libraries.Data.SnocList.SizeOf
import Libraries.Data.SnocList.Extra

||| Maping from a pairing of closed terms together with
||| their size (for efficiency) to the number of
||| occurences in toplevel definitions and flag for
||| whether it was encountered in delayed subexpression.
public export
UsageMap : Type
UsageMap = SortedMap (Integer, ClosedCExp) (Name, Integer, Bool)

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
||| to the corresponding expressions, if the expression
||| appears only in one place or is a subexpression of
||| some delayed expression.
public export
ReplaceMap : Type
ReplaceMap = SortedMap Name (ClosedCExp, Count, Bool)

toReplaceMap : UsageMap -> ReplaceMap
toReplaceMap = SortedMap.fromList
             . map (\((_,exp),(n,c,d)) => (n, (exp, C c, d)))
             . SortedMap.toList

--------------------------------------------------------------------------------
--          State
--------------------------------------------------------------------------------

data Sts : Type where

record St where
  constructor MkSt
  map : UsageMap
  idx : Int
  inDelay : Bool

-- Adds a new closed expression to the `UsageMap`
-- returning a new machine generated name to be used
-- if the expression should be lifted to the toplevel.
-- Very small expressions are being ignored.
store : Ref Sts St => Integer -> ClosedCExp -> Core (Maybe Name)
store sz exp =
  if sz < 5
     then pure Nothing
     else do
       (MkSt map idx inDelay)    <- get Sts

       (name,count,idx2,delayed) <-
         case lookup (sz,exp) map of
           Just (nm,cnt,delayed) => pure (nm, cnt+1, idx, delayed)
           Nothing       => pure (MN "csegen" idx, 1, idx + 1, inDelay)

       put Sts $ MkSt (insert (sz,exp) (name, count, inDelay || delayed) map) idx2 inDelay
       pure (Just name)

--------------------------------------------------------------------------------
--          Strengthening of Expressions
--------------------------------------------------------------------------------

dropVar : SizeOf inner
        -> {n : Nat}
        -> (0 p : IsVar x n (Scope.addInner outer inner))
        -> Maybe (Erased (IsVar x n inner))
dropVar inn p = case locateIsVar inn p of
  Right p => Just p
  Left p => Nothing


-- Tries to 'strengthen' an expression by removing an `outer` context.
-- This is typically invoked with `{inner = []}` which then grows when
-- going under binders.
0 Drop : Scoped -> Type
Drop tm
  = {0 inner, outer : Scope} ->
    SizeOf inner ->
    tm (Scope.addInner outer inner) ->
    Maybe (tm inner)


mutual
  dropCExp : Drop CExp
  dropCExp inn (CLocal {idx} fc p) = (\ q => CLocal fc (runErased q)) <$> dropVar inn p
  dropCExp inn (CRef fc x) = Just (CRef fc x)
  dropCExp inn (CLam fc x y) = CLam fc x <$> dropCExp (suc inn) y
  dropCExp inn (CLet fc x inlineOK y z) =
    CLet fc x inlineOK <$> dropCExp inn y <*> dropCExp (suc inn) z
  dropCExp inn (CApp fc x xs) = CApp fc <$> dropCExp inn x <*> traverse (dropCExp inn) xs
  dropCExp inn (CCon fc x y tag xs) = CCon fc x y tag <$> traverse (dropCExp inn) xs
  dropCExp inn (COp fc x xs) = COp fc x <$> traverse (dropCExp inn) xs
  dropCExp inn (CExtPrim fc p xs) = CExtPrim fc p <$> traverse (dropCExp inn) xs
  dropCExp inn (CForce fc x y) = CForce fc x <$> dropCExp inn y
  dropCExp inn (CDelay fc x y) = CDelay fc x <$> dropCExp inn y
  dropCExp inn (CConCase fc sc xs x) =
    CConCase fc                  <$>
    dropCExp inn sc              <*>
    traverse (dropConAlt inn) xs <*>
    traverse (dropCExp inn) x

  dropCExp inn (CConstCase fc sc xs x) =
    CConstCase fc                  <$>
    dropCExp inn sc                <*>
    traverse (dropConstAlt inn) xs <*>
    traverse (dropCExp inn) x

  dropCExp inn (CPrimVal fc x) = Just $ CPrimVal fc x
  dropCExp inn (CErased fc) = Just $ CErased fc
  dropCExp inn (CCrash fc x) = Just $ CCrash fc x

  dropConAlt : Drop CConAlt
  dropConAlt inn (MkConAlt x y tag args z) =
    MkConAlt x y tag args <$>
        dropCExp {outer=outer}
          (rewrite fishAsSnocAppend inner args in inn + mkSizeOf (cast args))
          (rewrite sym $ snocAppendFishAssociative outer inner args in z)

  dropConstAlt : Drop CConstAlt
  dropConstAlt inn (MkConstAlt x y) = MkConstAlt x <$> dropCExp inn y


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
  analyze c@(COp {})      = analyzeSubExp c
  analyze c@(CExtPrim {}) = analyzeSubExp c
  analyze c@(CForce {})   = analyzeSubExp c
  analyze c@(CDelay {})   = analyzeSubExp c

  analyze exp = do
    (sze, exp') <- analyzeSubExp exp
    case dropCExp zero exp' of
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
  analyzeSubExp e@(CLocal {}) = pure (1, e)
  analyzeSubExp e@(CRef {})   = pure (1, e)
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
    MkSt _ _ inDelay <- get Sts
    update Sts (\(MkSt map idx _) => MkSt map idx True)
    (sy, y') <- analyze y
    update Sts (\(MkSt map idx _) => MkSt map idx inDelay)
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

  analyzeSubExp c@(CPrimVal {}) = pure (1, c)
  analyzeSubExp c@(CErased {})  = pure (1, c)
  analyzeSubExp c@(CCrash {})   = pure (1, c)

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
analyzeDef (MkFun args x)   = MkFun args . snd <$> analyze x
analyzeDef d@(MkCon {})     = pure d
analyzeDef d@(MkForeign {}) = pure d
analyzeDef d@(MkError {})   = pure d

compileName :  Ref Ctxt Defs
            => Name
            -> Core (Maybe (Name, FC, CDef))
compileName fn = do
    defs <- get Ctxt
    Just def <- lookupCtxtExact fn (gamma defs)
        | Nothing => do log "compile.execute" 50 $ "Couldn't find " ++ show fn
                        pure Nothing
    let Just cexp = compexpr def
        | Nothing => do log "compile.execute" 50 $ "Couldn't compile " ++ show fn
                        pure Nothing
    pure $ Just (fn, location def, cexp)

--------------------------------------------------------------------------------
--          Replacing Expressions
--------------------------------------------------------------------------------

mutual
  -- During the analysis step, we replaced every closed
  -- expression with a machine generated name. We only
  -- want to keep these substitutions, if a closed term
  -- appears in several distinct locations in the code
  -- and does not appear inside `%delay`.
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
      Just (exp, Many, False) => do
        log "compiler.cse" 10 $ "  already replaced: Occurs many times"
        pure (CApp EmptyFC (CRef fc n) [])

      -- Expression count has already been checked, it occurs
      -- several times, but it has an occurrence inside `%delay`.
      -- Substitute the machine generated name with the original
      -- (CSE optimized) expression.
      Just (exp, Many, True) => do
        log "compiler.cse" 10 $ "  already replaced: Occurs inside %delay"
        -- pure (embed exp)
        pure (CForce EmptyFC LLazy (CApp EmptyFC (CRef fc n) []))

      -- Expression count has already been checked and occurs
      -- only once. Substitute the machine generated name with
      -- the original (but CSE optimized) exp
      Just (exp, Once, _) => do
        log "compiler.cse" 10 $ "  already replaced: Occurs once"
        pure (embed exp)

      -- Expression count has not yet been compared with the
      -- parent count. Do this now.
      Just (exp, C c, d)  => do
        log "compiler.cse" 10 $  "  expression of unknown quantity ("
                              ++ show c
                              ++ " occurences)"
        -- We first have to replace all child expressions.
        exp' <- replaceExp c exp
        if c > pc
           -- This is a common subexpression. We set its count to `Many`
           -- and inspect its occurence in delay to check whether it
           -- should be replaced or not.
           then do
             log "compiler.cse" 10 $ show n ++ " assigned quantity \"Many\""
             update ReplaceMap (insert n (exp', Many, d))
             case d of
                  False => pure (CApp EmptyFC (CRef fc n) [])
                  True => pure (CForce EmptyFC LLazy (CApp EmptyFC (CRef fc n) []))

           -- This expression occurs only once. We set its count to `Once`
           -- and keep it.
           else do
             log "compiler.cse" 10 $ show n ++ " assigned quantity \"Once\""
             update ReplaceMap (insert n (exp', Once, d))
             pure (embed exp')


  replaceExp :  Ref ReplaceMap ReplaceMap
             => Ref Ctxt Defs
             => (parentCount : Integer)
             -> CExp ns
             -> Core (CExp ns)
  replaceExp _ e@(CLocal {}) = pure e
  replaceExp pc (CRef f n)   = replaceRef pc f n
  replaceExp pc (CLam f n y) = CLam f n <$> replaceExp pc y
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

  replaceExp _ c@(CPrimVal {}) = pure c
  replaceExp _ c@(CErased {})  = pure c
  replaceExp _ c@(CCrash {})   = pure c

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
replaceDef (n, fc, d@(MkCon {}))     = pure (n, fc, d)
replaceDef (n, fc, d@(MkForeign {})) = pure (n, fc, d)
replaceDef (n, fc, d@(MkError {}))   = pure (n, fc, d)

newToplevelDefs : ReplaceMap -> List (Name, FC, CDef)
newToplevelDefs rm = mapMaybe toDef $ SortedMap.toList rm
  where toDef : (Name,(ClosedCExp,Count,Bool)) -> Maybe (Name, FC, CDef)
        toDef (nm,(exp,Many,False)) = Just (nm, EmptyFC, MkFun Scope.empty exp)
        toDef (nm,(exp,Many,True)) = Just (nm, EmptyFC, MkFun Scope.empty (CDelay EmptyFC LLazy exp))
        toDef _               = Nothing

undefinedCount : (Name, (ClosedCExp, Count)) -> Bool
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
  compilerDefs <- get Ctxt
  compiledDefs <- catMaybes <$> traverse compileName defs
  if compilerDefs.options.session.noCSE
    then pure (compiledDefs, me)
    else do
      log "compiler.cse" 10 $ "Analysing " ++ show (length defs) ++ " names"
      s            <- newRef Sts $ MkSt empty 0 False
      analyzedDefs <- traverse (traversePair (traversePair analyzeDef)) compiledDefs
      MkSt um _ _  <- get Sts
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
      let newDefs := newToplevelDefs replaceMap ++ replacedDefs
      pure (newDefs, replacedMain)
