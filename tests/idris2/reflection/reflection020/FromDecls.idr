import Data.List.Quantifiers

import Language.Reflection

import FromTTImp

%language ElabReflection

record NatDecl where
    constructor MkNatDecl
    var : String
    expr : NatExpr

natDecl : Decl -> Elab NatDecl
natDecl (IDef _ (UN (Basic nm)) [PatClause _ (IVar _ _) def]) = pure $ MkNatDecl nm !(natExpr def)
natDecl decl = fail "Invalid NatDecl"

natDecls : List Decl -> Elab (List NatDecl)
natDecls decls = traverse natDecl decls

namespace AsMacro
    %macro
    fromDecls : List Decl -> Elab (List NatDecl)
    fromDecls = natDecls

    export
    natDeclsMacroTest : List NatDecl
    natDeclsMacroTest = `[
        x = 1 + 2 + a
        y = 1 + 2 * 3 + 4
    ]

    failing "Invalid NatDecl"
        natDeclsInvalid : List NatDecl
        natDeclsInvalid = `[f x = 1 + 2]

    failing "Invalid NatDecl"
        natDeclsInvalid : List NatDecl
        natDeclsInvalid = `[x : 1]

namespace AsScript
    fromDecls : List Decl -> Elab (List NatDecl)
    fromDecls = natDecls

    export
    natDeclsScriptTest : List NatDecl
    natDeclsScriptTest = %runElab `[x = 1 + 2 * 3 + 4]

    failing "Invalid NatDecl"
        natDeclsInvalid : List NatDecl
        natDeclsInvalid = %runElab `[f x = 1 + 2]

namespace AsFunction
    data IsNatDecl : Decl -> Type where
        ItIsNatDecl : IsNatExpr def -> IsNatDecl (IDef fc1 (UN (Basic nm)) [PatClause fc2 (IVar fc3 (UN (Basic nm))) def])

    fromDecl : (decl : Decl) ->
               IsNatDecl decl =>
               NatDecl
    fromDecl @{ItIsNatDecl _} (IDef _ (UN (Basic nm)) [PatClause _ (IVar _ (UN (Basic nm))) def]) = MkNatDecl nm $ fromTTImp def

    fromDecls : (decls : List Decl) ->
                All IsNatDecl decls =>
                List NatDecl
    fromDecls [] = []
    fromDecls @{_ :: _} (decl :: decls) = fromDecl decl :: fromDecls decls

    export
    natDeclsFunctionTest : List NatDecl
    natDeclsFunctionTest = `[x = 1 + 2 * 3 + 4]

    failing "Can't find an implementation for All IsNatDecl"
        natDeclsInvalid : List NatDecl
        natDeclsInvalid = `[f x = 1 + 2]
