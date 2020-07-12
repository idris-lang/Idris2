module Compiler.ES.TailRec

import Compiler.ES.ImperativeAst

hasTailCall : Name -> ImperativeStatement -> Bool
hasTailCall n (SeqStatement x y) =
    hasTailCall n y
hasTailCall n (ReturnStatement x) =
    case x of
        IEApp (IEVar cn) _ => n == cn
        _ => False
hasTailCall n (SwitchStatement e alts d) =
    (any (\(_, w)=>hasTailCall n w) alts) || (maybe False (hasTailCall n) d)
hasTailCall n (ForEverLoop x) =
    hasTailCall n x
hasTailCall n o = False


argsName : Name
argsName = MN "tailRecOptimArgs" 0

stepFnName : Name
stepFnName = MN "tailRecOptimStep" 0

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

export
tailRecOptim :  ImperativeStatement -> ImperativeStatement
tailRecOptim (SeqStatement x y) = SeqStatement (tailRecOptim x) (tailRecOptim y)
tailRecOptim (FunDecl fc n args body) =
    let new_body = if hasTailCall n body then makeTailOptimToBody n args body
                        else body
    in FunDecl fc n args new_body
tailRecOptim x = x
