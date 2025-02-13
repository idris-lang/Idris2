import Language.Reflection

%language ElabReflection

decl : List Decl
decl = `[
  data Wrap : (phantom : Type) -> (a : Type) -> Type where
    -- whereas this will give us the right behaviour
    [search a]
    MkWrap : a -> Wrap ph a
]

%runElab declare decl

%hint
zero : Wrap Bool Nat
zero = MkWrap 0

getWrappedVal : Wrap ph a => a
getWrappedVal @{MkWrap w} = w

test : Main.getWrappedVal === Z
test = Refl
