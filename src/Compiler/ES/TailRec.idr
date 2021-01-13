module Compiler.ES.TailRec

import Data.Maybe
import Data.List
import Data.Strings
import Data.SortedSet
import Data.SortedMap
import Core.Name
import Core.Context
import Compiler.ES.ImperativeAst

import Debug.Trace

data TailRecS : Type where

record TailSt where
  constructor MkTailSt
  nextName : Int

genName : {auto c : Ref TailRecS TailSt} -> Core Name
genName =
  do
    s <- get TailRecS
    let i = nextName s
    put TailRecS (record { nextName = i + 1 } s)
    pure $ MN "imp_gen_tailoptim" i

allTailCalls : ImperativeStatement -> SortedSet Name
allTailCalls (SeqStatement x y) =
    allTailCalls y
allTailCalls (ReturnStatement x) =
    case x of
        IEApp (IEVar n) _ => insert n empty
        _ => empty
allTailCalls (SwitchStatement e alts d) =
    maybe empty allTailCalls d `union` concat (map allTailCalls (map snd alts))
allTailCalls (ForEverLoop x) =
    allTailCalls x
allTailCalls o = empty


argsName : Name
argsName = MN "imp_gen_tailoptim_Args" 0

stepFnName : Name
stepFnName = MN "imp_gen_tailoptim_step" 0

fusionArgsName : Name
fusionArgsName = MN "imp_gen_tailoptim_fusion_args" 0

createNewArgs : List ImperativeExp -> ImperativeExp
createNewArgs values =
    IEConstructor (Left 0) values


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
    SwitchStatement e (map (\(x,y) => (x, replaceTailCall n y)) alts) (map (replaceTailCall n) d)
replaceTailCall n (ForEverLoop x) =
    ForEverLoop $ replaceTailCall n x
replaceTailCall n o = o

makeTailOptimToBody : Name -> List Name -> ImperativeStatement -> ImperativeStatement
makeTailOptimToBody n argNames body =
    let lastArg = (length argNames) + 1
        newArgExp = map (\x => IEConstructorArg (cast x) (IEVar argsName)) [1..lastArg]
        bodyArgsReplaced = replaceNamesExpS (zip argNames newArgExp) body
        stepBody = replaceTailCall n bodyArgsReplaced
        stepFn = FunDecl EmptyFC stepFnName [argsName] stepBody
        loopRec = MutateStatement argsName (IEApp (IEVar stepFnName) [IEVar argsName])
        loopReturn = ReturnStatement (IEConstructorArg 1 $ IEVar argsName)
        loop = ForEverLoop $ SwitchStatement (IEConstructorHead $ IEVar argsName) [(IEConstructorTag $ Left 0, loopRec)] (Just loopReturn)
    in stepFn <+> createArgInit argNames <+> loop

record CallGraph where
    constructor MkCallGraph
    calls, callers : SortedMap Name (SortedSet Name)

showCallGraph : CallGraph -> String
showCallGraph x =
    let calls = unlines $ map
                    (\(x,y) => show x ++ ": " ++ show (SortedSet.toList y))
                    (SortedMap.toList x.calls)
        callers = unlines $ map
                    (\(x,y) => show x ++ ": " ++ show (SortedSet.toList y))
                    (SortedMap.toList x.callers)
    in calls ++ "\n----\n" ++ callers


tailCallGraph : ImperativeStatement -> CallGraph
tailCallGraph (SeqStatement x y) =
    let xg = tailCallGraph x
        yg = tailCallGraph y
    in MkCallGraph
        (mergeWith union xg.calls yg.calls)
        (mergeWith union xg.callers yg.callers)
tailCallGraph (FunDecl fc n args body) =
    let calls = allTailCalls body
    in MkCallGraph (insert n calls empty) (SortedMap.fromList $ map (\x => (x, SortedSet.insert n empty)) (SortedSet.toList calls))
tailCallGraph _ = MkCallGraph empty empty

kosarajuL : SortedSet Name -> List Name -> CallGraph -> (SortedSet Name, List Name)
kosarajuL visited [] graph =
    (visited, [])
kosarajuL visited (x::xs) graph =
    if contains x visited then kosarajuL visited xs graph
        else let outNeighbours = maybe [] SortedSet.toList $ lookup x (graph.calls)
                 (visited_, l_) = kosarajuL (insert x visited) (toList outNeighbours) graph
                 (visited__, l__) = kosarajuL visited_ xs graph
             in (visited__, l__ ++ (x :: l_))



kosarajuAssign : CallGraph -> Name -> Name -> SortedMap Name Name -> SortedMap Name Name
kosarajuAssign graph u root s =
    case lookup u s of
        Just _ => s
        Nothing => let inNeighbours = maybe [] SortedSet.toList $ lookup u (graph.callers)
                   in foldl (\acc, elem => kosarajuAssign graph elem root acc) (insert u root s) inNeighbours

kosaraju: CallGraph -> SortedMap Name Name
kosaraju graph =
    let l = snd $ kosarajuL empty (keys $ graph.calls) graph
    in foldl (\acc, elem => kosarajuAssign graph elem elem acc) empty l

groupBy : (a -> a -> Bool) -> List a -> List (List a)
groupBy _ [] = []
groupBy p' (x'::xs') =
    let (ys',zs') = go p' x' xs'
    in (x' :: ys') :: zs'
    where
        go : (a -> a -> Bool) -> a -> List a -> (List a, List (List a))
        go p z (x::xs) =
            let (ys,zs) = go p x xs
            in case p z x of
                True => (x :: ys, zs)
                False => ([], (x :: ys) :: zs)
        go _ _ [] = ([], [])

recursiveTailCallGroups : CallGraph -> List (List Name)
recursiveTailCallGroups graph =
    let roots = kosaraju graph
        groups = map (map fst) $
                 groupBy (\x,y => Builtin.snd x == Builtin.snd y) $
                 sortBy (\x,y=> compare (snd x) (snd y)) $
                 toList roots
    in [x | x<-groups, hasTailCalls x]
    where
        hasTailCalls : List Name -> Bool
        hasTailCalls [] =
            False
        hasTailCalls [x] =
            case lookup x (graph.calls) of
                Nothing =>
                    False
                Just s =>
                    case SortedSet.toList s of
                        [n] => n == x
                        _   => False
        hasTailCalls _ =
            True


extractFunctions : SortedSet Name -> ImperativeStatement ->
                     (ImperativeStatement, SortedMap Name (FC, List Name, ImperativeStatement))
extractFunctions toExtract (SeqStatement x y) =
    let (xs, xf) = extractFunctions toExtract x
        (ys, yf) = extractFunctions toExtract y
    in (xs <+> ys, mergeLeft xf yf)
extractFunctions toExtract f@(FunDecl fc n args body) =
    if contains n toExtract then (neutral, insert n (fc, args, body) empty)
        else (f, empty)
extractFunctions toExtract x =
    (x, empty)

getDef : SortedMap Name (FC, List Name, ImperativeStatement) -> Name -> Core (FC, List Name, ImperativeStatement)
getDef defs n =
    case lookup n defs of
        Nothing => throw $ (InternalError $ "Can't find function definition in tailRecOptim")
        Just x => pure x


makeFusionBranch : Name -> List (Name, Nat) ->  (Nat, FC, List Name, ImperativeStatement) ->
                         (ImperativeExp, ImperativeStatement)
makeFusionBranch fusionName functionsIdx (i, _, args, body) =
    let newArgExp = map (\i => IEConstructorArg (cast i) (IEVar fusionArgsName))  [1..(length args)]
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

changeBodyToUseFusion : Name -> (Nat, Name, FC, List Name, ImperativeStatement) -> ImperativeStatement
changeBodyToUseFusion fusionName (i, n, (fc, args, _)) =
    FunDecl fc n args (ReturnStatement $ IEApp (IEVar fusionName) [IEConstructor (Left $ cast i) (map IEVar args)])

tailRecOptimGroup : {auto c : Ref TailRecS TailSt} ->
                      SortedMap Name (FC, List Name, ImperativeStatement) ->
                        List Name -> Core ImperativeStatement
tailRecOptimGroup defs [] = pure neutral
tailRecOptimGroup defs [n] =
    do
        (fc, args , body) <- getDef defs n
        pure $ FunDecl fc n args (makeTailOptimToBody n args body)
tailRecOptimGroup defs names =
    do
        fusionName <- genName
        d <- traverse (getDef defs) names
        let ids = [0..(length names `minus` 1)]
        let alts = map (makeFusionBranch fusionName (zip names ids)) (zip ids d)
        let fusionBody = SwitchStatement
                           (IEConstructorHead $ IEVar fusionArgsName)
                           alts
                           Nothing
        let fusionArgs = [fusionArgsName]
        let fusion = FunDecl EmptyFC fusionName fusionArgs (makeTailOptimToBody fusionName fusionArgs fusionBody)
        let newFunctions = Prelude.concat $ map
                            (changeBodyToUseFusion fusionName)
                            (ids `List.zip` (names `List.zip` d))
        pure $ fusion <+> newFunctions



export
tailRecOptim :  ImperativeStatement -> Core ImperativeStatement
tailRecOptim x =
    do
        newRef TailRecS (MkTailSt 0)
        let graph = tailCallGraph x
        let groups =  recursiveTailCallGroups graph
        let functionsToOptimize = foldl SortedSet.union empty $ map SortedSet.fromList groups
        let (unchanged, defs) = extractFunctions functionsToOptimize x
        optimized <- traverse (tailRecOptimGroup defs) groups
        pure $ unchanged <+> (concat optimized)
