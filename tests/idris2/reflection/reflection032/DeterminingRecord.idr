import Language.Reflection

%language ElabReflection

decl : List Decl
decl = `[
  record Wrap (phantom : Type) (a : Type) where
    -- whereas this will give us the right behaviour
    [search a]
    constructor MkWrap
    unWrap : a
]

%runElab declare decl

%hint
zero : Wrap Bool Nat
zero = MkWrap 0

getWrappedVal : Wrap ph a => a
getWrappedVal @{w} = unWrap w

test : Main.getWrappedVal === Z
test = Refl
