import Language.Reflection

%language ElabReflection

public export
data NatExpr : Type where
     Plus : NatExpr -> NatExpr -> NatExpr
     Mult : NatExpr -> NatExpr -> NatExpr
     Val : Nat -> NatExpr
     Var : String -> NatExpr

public export
natExpr : TTImp -> Elab NatExpr
natExpr `(~(l) + ~(r)) = [| Plus (natExpr l) (natExpr r) |]
natExpr `(~(l) * ~(r)) = [| Mult (natExpr l) (natExpr r) |]
natExpr `(fromInteger ~(IPrimVal _ (BI n))) = pure $ Val $ fromInteger n
natExpr (IVar _ (UN (Basic nm))) = pure $ Var nm
natExpr s = failAt (getFC s) "Invalid NatExpr"

namespace AsMacro
    %macro
    fromTTImp : TTImp -> Elab NatExpr
    fromTTImp = natExpr

    export
    natExprMacroTest : NatExpr
    natExprMacroTest = `(1 + 2 + x)

    export
    natExprPrecedenceTest : NatExpr
    natExprPrecedenceTest = `(1 + 2 * 3 + 4)

    failing "Invalid NatExpr"
        natExprInvalid : NatExpr
        natExprInvalid = `(f x)

namespace AsScript
    fromTTImp : TTImp -> Elab NatExpr
    fromTTImp = natExpr

    export
    natExprScriptTest : NatExpr
    natExprScriptTest = %runElab `(3 + 4)

    failing "Invalid NatExpr"
        natExprInvalid : NatExpr
        natExprInvalid = %runElab `(f x)

namespace AsFunction
    public export
    data IsNatExpr : TTImp -> Type where
        IsPlus : IsNatExpr l -> IsNatExpr r -> IsNatExpr (IApp fc1 (IApp fc2 (IVar fc3 (UN (Basic "+"))) l) r)
        IsMult : IsNatExpr l -> IsNatExpr r -> IsNatExpr (IApp fc1 (IApp fc2 (IVar fc3 (UN (Basic "*"))) l) r)
        IsVal : (n : Integer) -> IsNatExpr (IApp fc1 (IVar fc2 (UN (Basic "fromInteger"))) (IPrimVal fc3 (BI n)))

    export
    fromTTImp : (0 s : TTImp) ->
                IsNatExpr s =>
                NatExpr
    fromTTImp (IApp _ (IApp _ (IVar _ (UN (Basic "+"))) l) r) @{IsPlus _ _} = Plus (fromTTImp l) (fromTTImp r)
    fromTTImp (IApp _ (IApp _ (IVar _ (UN (Basic "*"))) l) r) @{IsMult _ _} = Mult (fromTTImp l) (fromTTImp r)
    fromTTImp (IApp _ (IVar _ (UN (Basic "fromInteger"))) (IPrimVal _ (BI n))) @{IsVal n} = Val $ cast n

    export
    natExprFunctionTest : NatExpr
    natExprFunctionTest = `(1 + 2 * 3 + 4)

    failing "Can't find an implementation for IsNatExpr"
        natExprInvalid : NatExpr
        natExprInvalid = `(f x)
