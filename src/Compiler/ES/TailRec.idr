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


createArgUpdates : List Name -> List ImperativeExp -> ImperativeStatement
createArgUpdates names values =
    let tempArgNames = map (\x => MN "tailRepOptim" (cast x)) [0..(length names)]
        setTemps = concat $ map (\(x,y) => LetDecl x (Just y)) (zip tempArgNames values)
        setArgs = concat $ map (\(x,y) => MutateStatement x (IEVar y)) (zip names tempArgNames)
    in setTemps <+> setArgs


replaceTailCall : List Name -> Name -> ImperativeStatement -> ImperativeStatement
replaceTailCall args n (SeqStatement x y) = SeqStatement x (replaceTailCall args n y)
replaceTailCall args n (ReturnStatement x) =
    case x of
        IEApp (IEVar cn) arg_vals =>
            if n == cn then createArgUpdates args arg_vals
                else ReturnStatement x
        _ => ReturnStatement x
replaceTailCall args n (SwitchStatement e alts d) =
    SwitchStatement e (map (\(x,y) => (x, replaceTailCall args n y)) alts) (map (replaceTailCall args n) d)
replaceTailCall args n (ForEverLoop x) =
    ForEverLoop $ replaceTailCall args n x
replaceTailCall args n o = o

export
tailRecOptim :  ImperativeStatement -> ImperativeStatement
tailRecOptim (SeqStatement x y) = SeqStatement (tailRecOptim x) (tailRecOptim y)
tailRecOptim (FunDecl fc n args body) =
    let new_body = if hasTailCall n body then ForEverLoop (replaceTailCall args n body)
                        else body
    in FunDecl fc n args new_body
tailRecOptim x = x
