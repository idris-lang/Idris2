module Data.Path

%default total

||| Paths in a typed graph as a sequence of edges with source and target nodes matching up domino-style.
||| AKA reflexive-transitive closure.
public export
data Path : (t -> t -> Type) -> t -> t -> Type where
  Nil  : Path g i i
  (::) : {0 i, j, k : t} ->
         g i j -> Path g j k -> Path g i k

export
joinPath : Path g i j -> Path g j k -> Path g i k
joinPath []      jk = jk
joinPath (e::ij) jk = e :: joinPath ij jk

export
snocPath : Path g i j -> g j k -> Path g i k
snocPath []      f = [f]
snocPath (e::ij) f = e :: snocPath ij f

export
lengthPath : Path g i j -> Nat
lengthPath []     = Z
lengthPath (_::p) = S $ lengthPath p

export
mapPath : {0 gt : t -> t -> Type} -> {0 gu : u -> u -> Type} -> {0 f : t -> u}
       -> ({0 i, j : t} ->      gt i j ->      gu (f i) (f j))
       ->  {0 i, j : t} -> Path gt i j -> Path gu (f i) (f j)
mapPath gf []     = []
mapPath gf (e::p) = gf e :: mapPath gf p

export
foldPath : {0 gt : t -> t -> Type} -> {0 gu : u -> u -> Type} -> {0 f : t -> u}
        -> ({0 i, j, k : t} ->      gt i j -> gu (f j) (f k) -> gu (f i) (f k))
        ->  {0 i, j, k : t} -> Path gt i j -> gu (f j) (f k) -> gu (f i) (f k)
foldPath gf []      jk = jk
foldPath gf (e::ij) jk = gf e (foldPath {gu} gf ij jk)

export
foldlPath : {0 gt : t -> t -> Type} -> {0 gu : u -> u -> Type} -> {0 f : t -> u}
        -> ({0 i, j, k : t} -> gu (f i) (f j) ->      gt j k -> gu (f i) (f k))
        ->  {0 i, j, k : t} -> gu (f i) (f j) -> Path gt j k -> gu (f i) (f k)
foldlPath gf ij []      = ij
foldlPath gf ij (e::jk) = foldlPath {gu} gf (gf ij e) jk
