module Syntax.Inspect

public export
record Reveal {0 a : Type} {0 b : a -> Type}
              (f : (x : a) -> b x) (x : a) (y : b x) where
  constructor MkReveal
  proof : f x === y

||| An alternative for 'Syntax.WithProof' that allows to keep the
||| proof certificate in non-reduced form after nested matching.
||| Inspired by https://agda.github.io/agda-stdlib/README.Inspect.html
public export
inspect : {0 a : Type} -> {0 b : a -> Type} ->
          (f : (x : a) -> b x) -> (x : a) -> Reveal f x (f x)
inspect f x = MkReveal Refl
