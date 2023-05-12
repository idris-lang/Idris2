||| The contents of this module are based on the paper
||| Deferring the Details and Deriving Programs
||| by Liam O'Connor
||| https://doi.org/10.1145/3331554.3342605
module Data.ProofDelay

%default total

namespace HList
  ||| Heterogeneous list indexed by list of types of every element.
  |||
  ||| [21](https://doi.org/10.1145/1017472.1017488)
  public export
  data HList : List Type -> Type where
    Nil  : HList []
    (::) : {0 s : _} -> {0 ss : _} -> s -> HList ss -> HList (s :: ss)

  ||| Similar to `take` for normal lists, except for the index.
  public export
  takeH : {ss : _} -> HList (ss ++ ts) -> HList ss
  takeH {ss = []} ys = []
  takeH {ss = (s :: ss)} (x :: xs) = x :: takeH xs

  ||| Similar to `drop` for normal lists, except for the index.
  public export
  dropH : {ss : _} -> HList (ss ++ ts) -> HList ts
  dropH {ss = []} ys = ys
  dropH {ss = (s :: ss)} (x :: xs) = dropH xs


||| A type `x` which can only be computed once some, delayed, proof obligations
||| have been fulfilled.
public export
record PDelay (x : Type) where
  constructor Prf

  ||| List of propositions we need to prove.
  goals : List Type

  ||| Given the proofs required (i.e. the goals), actually compute the value x.
  prove : HList goals -> x


||| A value which can immediately be constructed (i.e. no delayed proofs).
public export
pure : tx -> PDelay tx
pure x = Prf [] (const x)

||| Delay the full computation of `x` until `later`.
public export
later : (tx : _) -> PDelay tx
later tx = Prf (tx :: []) (\(x :: []) => x)

-- pronounced "apply"
||| We can compose `PDelay` computations.
public export
(<*>) : PDelay (a -> b) -> PDelay a -> PDelay b
(Prf goals1 prove1) <*> (Prf goals2 prove2) =
  Prf (goals1 ++ goals2) (\hl => prove1 (takeH hl) (prove2 (dropH hl)))

