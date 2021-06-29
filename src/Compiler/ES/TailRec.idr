||| Tail-call optimization.
|||
||| Here is a lengthy explanation how this works at the
||| moment. Assume the following call graph of functions f1,f2,f3,f4 all
||| calling each other in tail call position:
|||
||| ```
|||       ------------ f2 ---- f4 (result)
|||      /          /     \
||| f1 ---- f1     /       -- f1
|||      \        /
|||       -- f3 --
||| ```
|||
||| Function `tailCallGraph` creates a directed graph of all toplevel
||| function calls (incoming and outgoing) in tail-call position:
|||
||| ```idris
||| MkCallGraph $ fromList [(f1,[f1,f2,f3]),(f2,[f1,f4]),(f3,[f2])]
|||             $ fromList [(f1,[f1,f2]),(f2,[f1,f3]),(f3,[f1]),(f4,[f2])]
||| ```
|||
||| Mutually tail-recursive functions form a strongly connected
||| component in such a call graph: There is a (directed) path from every function
||| to every other function. Kosaraju's algorithm is used to identify
||| these strongly connected components by mapping every function
||| of a strongly connected component to the same representative (called `root`)
||| of its component. In the above case, this would result in a sorted
||| map of the following structure:
|||
|||
||| ```idris
||| fromList [(f1,f1),(f1,f2),(f1,f3),(f4,f4)]
||| ```idris
|||
||| As can be seen, f1,f2, and f3 all point to the same root (f1), while
||| f4 points to a different root.
|||
||| Such a tail-recursive call graph is now converted to an imperative
||| loop as follows: Let `obj0={h:0, a1:...}` be a Javascript object consisting
||| of a tag `h` and an argument `a1`. `h` indicates, whether `obj0.a1`
||| contains the result of the computation (`h = 1`) or describes
||| a continuation indicating the next function to invoke
||| together with the necessary arguments. A single `step`
||| function will take such an object and use `a1` in a switch
||| statement to decide , which function
||| implementation to invoke (f1,f2,f3).
||| The result will be a new object, again indicating in tag `h`, whether
||| we arrived at a result, or we need to continue looping.
|||
||| Here is a cleaned-up and simplified version of the Javascript code
||| generated:
|||
||| ```javascript
||| function imp_gen_tailoptim_0(imp_gen_tailoptim_fusion_args_0){//EmptyFC
|||  function imp_gen_tailoptim_step_0(obj0){
|||   switch(obj0.a1.h){
|||    case 0: ... //implementation of a single step of f1
|||                //taking its arguments from the fields of `obj0.a1`.
|||    case 1: ... //implementation of a single step of f2
|||    case 2: ... //implementation of a single step of f3
|||   }
|||  }
|||
|||  // initial object containing the arguments for the first
|||  // function call
|||  obj0 = ({h:0, a1: imp_gen_tailoptim_fusion_args_0});
|||
|||  // infinite loop running until `obj0.h != 0`.
|||  while(true){
|||   switch(obj0.h){
|||    case 0: {
|||     obj0 = imp_gen_tailoptim_step_0(obj0);
|||     break; }
|||    default:
|||     return obj0.a1;
|||   }
|||  }
||| }
||| ```
module Compiler.ES.TailRec

import Data.Maybe
import Data.List
import Data.List1
import Data.String
import Libraries.Data.Graph
import Libraries.Data.SortedSet
import Libraries.Data.List.Extra as L
import Libraries.Data.SortedSet
import Libraries.Data.SortedMap
import Core.Name
import Core.Context
import Compiler.ES.ImperativeAst

import Debug.Trace

%default covering

data TailRecS : Type where

record TailSt where
  constructor MkTailSt
  nextName : Int

genName : {auto c : Ref TailRecS TailSt} -> Core Name
genName =
  do s <- get TailRecS
     let i = nextName s
     put TailRecS (record { nextName = i + 1 } s)
     pure $ MN "imp_gen_tailoptim" i

-- returns the set of tail calls made from a given
-- imperative statement.
allTailCalls : ImperativeStatement -> SortedSet Name
allTailCalls (SeqStatement x y)  = allTailCalls y
allTailCalls (ReturnStatement $ IEApp (IEVar n) _) = singleton n
allTailCalls (SwitchStatement e alts d) =
  concatMap allTailCalls d `union` concatMap (allTailCalls . snd) alts
allTailCalls (ForEverLoop x) = allTailCalls x
allTailCalls o = empty

argsName : Name
argsName = MN "imp_gen_tailoptim_Args" 0

stepFnName : Name
stepFnName = MN "imp_gen_tailoptim_step" 0

fusionArgsName : Name
fusionArgsName = MN "imp_gen_tailoptim_fusion_args" 0

createNewArgs : List ImperativeExp -> ImperativeExp
createNewArgs = IEConstructor (Left 0)

createArgInit : List Name -> ImperativeStatement
createArgInit names =
    LetDecl argsName (Just $ IEConstructor (Left 0) (map IEVar names))

replaceTailCall : Name -> ImperativeStatement -> ImperativeStatement
replaceTailCall n (SeqStatement x y) = SeqStatement x (replaceTailCall n y)
replaceTailCall n (ReturnStatement x) =
    let defRet = ReturnStatement $ IEConstructor (Left 1) [x]
    in case x of
        IEApp (IEVar cn) arg_vals =>
            if n == cn then ReturnStatement $ createNewArgs arg_vals
                else defRet
        _ => defRet
replaceTailCall n (SwitchStatement e alts d) =
    SwitchStatement e (map (mapSnd $ replaceTailCall n) alts)
                      (map (replaceTailCall n) d)
replaceTailCall n (ForEverLoop x) =
    ForEverLoop $ replaceTailCall n x
replaceTailCall n o = o

-- generates the tailcall-optimized function body
makeTailOptimToBody :  Name
                    -> List Name
                    -> ImperativeStatement
                    -> ImperativeStatement
makeTailOptimToBody n argNames body =
    let newArgExp = map (\x => IEConstructorArg (cast x) (IEVar argsName)) [1..length argNames]
        bodyArgsReplaced = replaceNamesExpS (zip argNames newArgExp) body
        stepBody = replaceTailCall n bodyArgsReplaced

        -- single step function. This takes a single argument
        -- and returns a new object indicating whether to continue looping
        -- or to return a result.
        stepFn = FunDecl EmptyFC stepFnName [argsName] stepBody

        -- calls the step function and mutates the loop object with the result
        loopRec = MutateStatement argsName (IEApp (IEVar stepFnName) [IEVar argsName])

        -- returns field `a1` from the loop object.
        loopReturn = ReturnStatement (IEConstructorArg 1 $ IEVar argsName)

        -- switch on the constructor head and either continue looping or
        -- return the result
        loop = ForEverLoop
             $ SwitchStatement (IEConstructorHead $ IEVar argsName)
                               [(IEConstructorTag $ Left 0, loopRec)]
                               (Just loopReturn)
    in stepFn <+> createArgInit argNames <+> loop

-- when creating the tail call graph, we only process
-- function declarations and we are only interested
-- in calls being made at tail position
tailCallGraph : ImperativeStatement -> SortedMap Name (SortedSet Name)
tailCallGraph (SeqStatement x y) =
  mergeWith union (tailCallGraph x) (tailCallGraph y)

tailCallGraph (FunDecl fc n args body) =
  singleton n $ allTailCalls body

tailCallGraph _ = empty

-- lookup up the list of values associated with
-- a given key (`Nil` if the key is not present in the list)
lookupList : k -> SortedMap k (SortedSet b) -> List b
lookupList v = maybe [] SortedSet.toList . lookup v

recursiveTailCallGroups : SortedMap Name (SortedSet Name) -> List (List Name)
recursiveTailCallGroups graph =
  [forget x | x <-tarjan graph, hasTailCalls x]

    -- in case of larger groups (more than one element)
    -- the group contains tailcalls by construction. In case
    -- of a single function, we need to check that at least one
    -- outgoing tailcall goes back to the function itself.
    where hasTailCalls : List1 Name -> Bool
          hasTailCalls (x ::: Nil) = x `elem` lookupList x graph
          hasTailCalls _           = True

-- extracts the functions belonging to the given tailcall
-- group from the given imperative statement, thereby removing
-- them from the given statement.
extractFunctions :  (tailCallGroup : SortedSet Name)
                 -> ImperativeStatement
                 -> ( ImperativeStatement
                    , SortedMap Name (FC, List Name, ImperativeStatement)
                    )
extractFunctions toExtract (SeqStatement x y) =
    let (xs, xf) = extractFunctions toExtract x
        (ys, yf) = extractFunctions toExtract y
    in (xs <+> ys, mergeLeft xf yf)
extractFunctions toExtract f@(FunDecl fc n args body) =
    if contains n toExtract then (neutral, insert n (fc, args, body) empty)
        else (f, empty)
extractFunctions toExtract x =
    (x, empty)

-- lookup a function definition, throwing a compile-time error
-- if none is found
getDef :  SortedMap Name (FC, List Name, ImperativeStatement)
       -> Name
       -> Core (FC, List Name, ImperativeStatement)
getDef defs n =
    case lookup n defs of
        Nothing => throw $ (InternalError $ "Can't find function definition in tailRecOptim")
        Just x => pure x

makeFusionBranch :  Name
                 -> List (Name, Nat)
                 -> (Nat, FC, List Name, ImperativeStatement)
                 -> (ImperativeExp, ImperativeStatement)
makeFusionBranch fusionName functionsIdx (i, _, args, body) =
    let newArgExp = map (\i => IEConstructorArg (cast i) (IEVar fusionArgsName))
                        [1..length args]
        bodyRepArgs = replaceNamesExpS (zip args newArgExp) body
    in (IEConstructorTag $ Left $ cast i, replaceExpS rep bodyRepArgs)
    where
        rep : ImperativeExp -> Maybe ImperativeExp
        rep (IEApp (IEVar n) arg_vals) =
            case lookup n functionsIdx of
                Nothing => Nothing
                Just i => Just $ IEApp
                          (IEVar fusionName)
                          [IEConstructor (Left $ cast i) arg_vals]
        rep _ = Nothing

changeBodyToUseFusion :  Name
                      -> (Nat, Name, FC, List Name, ImperativeStatement)
                      -> ImperativeStatement
changeBodyToUseFusion fusionName (i, n, (fc, args, _)) =
    FunDecl fc n args (ReturnStatement $ IEApp (IEVar fusionName)
                        [IEConstructor (Left $ cast i) (map IEVar args)])

tailRecOptimGroup :  {auto c : Ref TailRecS TailSt}
                  -> SortedMap Name (FC, List Name, ImperativeStatement)
                  -> List Name -> Core ImperativeStatement
tailRecOptimGroup defs [] = pure neutral
tailRecOptimGroup defs [n] =
    do (fc, args , body) <- getDef defs n
       pure $ FunDecl fc n args (makeTailOptimToBody n args body)

tailRecOptimGroup defs names =
    do fusionName <- genName
       d <- traverse (getDef defs) names
       let ids = [0..(length names `minus` 1)]
       let alts = map (makeFusionBranch fusionName (zip names ids)) (zip ids d)
       let fusionBody = SwitchStatement
                          (IEConstructorHead $ IEVar fusionArgsName)
                          alts
                          Nothing
       let fusionArgs = [fusionArgsName]
       let fusion = FunDecl EmptyFC
                            fusionName
                            fusionArgs
                            (makeTailOptimToBody fusionName fusionArgs fusionBody)
       let newFunctions = Prelude.concat $ map
                           (changeBodyToUseFusion fusionName)
                           (ids `zip` (names `zip` d))
       pure $ fusion <+> newFunctions

||| (Mutual) Tail recursion optimizations: Converts all groups of
||| mutually tail recursive functions to an imperative loop.
export
tailRecOptim : ImperativeStatement -> Core ImperativeStatement
tailRecOptim x =
    do ref <- newRef TailRecS (MkTailSt 0)
       let groups = recursiveTailCallGroups (tailCallGraph x)
       let functionsToOptimize = foldl SortedSet.union empty $ map SortedSet.fromList groups
       let (unchanged, defs) = extractFunctions functionsToOptimize x
       optimized <- traverse (tailRecOptimGroup defs) groups
       pure $ unchanged <+> (concat optimized)
