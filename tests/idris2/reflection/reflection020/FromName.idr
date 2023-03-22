import Language.Reflection

%language ElabReflection

data MyName = MkMyName String

myName : Name -> Elab MyName
myName (UN (Basic nm)) = pure $ MkMyName nm
myName nm = fail "Invalid MyName"

namespace AsMacro
    %macro
    fromName : Name -> Elab MyName
    fromName = myName

    export
    myNameMacroTest : MyName
    myNameMacroTest = `{x}

    failing "Invalid MyName"
        myNameInvalid : MyName
        myNameInvalid = `{A.x}

namespace AsScript
    fromName : Name -> Elab MyName
    fromName = myName

    export
    myNameScriptTest : MyName
    myNameScriptTest = %runElab `{y}

    failing "Invalid MyName"
        myNameInvalid : MyName
        myNameInvalid = %runElab `{A.y}

namespace AsFunction
    data IsMyName : Name -> Type where
        ItIsMyName : IsMyName (UN (Basic nm))

    fromName : (nm : Name) ->
               IsMyName nm =>
               MyName
    fromName (UN (Basic nm)) @{ItIsMyName} = MkMyName nm

    export
    myNameFunctionTest : MyName
    myNameFunctionTest = `{z}

    failing "Can't find an implementation for IsMyName"
        myNameInvalid : MyName
        myNameInvalid = `{A.z}
