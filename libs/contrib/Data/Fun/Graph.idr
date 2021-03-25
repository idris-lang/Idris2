module Data.Fun.Graph

||| A relation corresponding to the graph of `f`.
public export
record Graph {0 a : Type} {0 b : a -> Type}
             (f : (x : a) -> b x) (x : a) (y : b x) where
  constructor MkGraph
  equality : f x === y

||| An alternative for 'Syntax.WithProof' that allows to keep the
||| proof certificate in non-reduced form after nested matching.
||| Inspired by https://agda.github.io/agda-stdlib/README.Inspect.html
public export
remember : {0 a : Type} -> {0 b : a -> Type} ->
           (f : (x : a) -> b x) -> (x : a) -> Graph f x (f x)
remember f x = MkGraph Refl
