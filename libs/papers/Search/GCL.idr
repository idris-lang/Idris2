||| The content of this module is based on the paper
||| Applications of Applicative Proof Search
||| by Liam O'Connor
||| https://doi.org/10.1145/2976022.2976030

module Search.GCL

import Data.Nat
import Data.List.Lazy
import Data.List.Quantifiers
import Data.List.Lazy.Quantifiers

import public Search.Negation
import public Search.HDecidable
import public Search.Properties
import public Search.CTL

%default total

parameters (Sts : Type)
  mutual
    ||| Guarded Command Language
    public export
    data GCL : Type where
      IF : (gs : List GUARD) -> GCL

      DOT : GCL -> GCL -> GCL

      DO : (gs : List GUARD) -> GCL

      UPDATE : (u : Sts -> Sts) -> GCL

      ||| Termination
      SKIP : GCL

    ||| A predicate
    public export
    Pred : Type
    Pred = (st : Sts) -> Bool

    public export
    record GUARD where
      constructor MkGUARD
      g : Pred
      x : GCL

  public export
  Uninhabited (IF _ === SKIP) where
    uninhabited Refl impossible

  public export
  Uninhabited (DOT _ _ === SKIP) where
    uninhabited Refl impossible

  public export
  Uninhabited (DO _ === SKIP) where
    uninhabited Refl impossible

  public export
  Uninhabited (UPDATE _ === SKIP) where
    uninhabited Refl impossible

  ||| Prove that the given program terminated (i.e. reached a `SKIP`).
  public export
  isSkip : (l : GCL) -> Dec (l === SKIP)
  isSkip (IF xs)     = No absurd
  isSkip (DOT y z)   = No absurd
  isSkip (DO xs)     = No absurd
  isSkip (UPDATE uf) = No absurd
  isSkip SKIP        = Yes Refl

  ||| Operational sematics of GCL
  public export
  covering
  ops : (GCL, Sts) -> List (GCL, Sts)
  ops (SKIP, st) = []
  ops ((UPDATE u), st) = [(SKIP, u st)]
  ops ((DOT SKIP y), st) = [(y, st)]
  ops ((DOT x y), st) = map (\ (x, st') => ((DOT x y), st')) $
                        ops (x, st)
  ops ((IF gs), st) = map (\ aGuard => (aGuard.x, st)) $
                      filter (\ aGuard => aGuard.g st) gs

  ops ((DO gs), st) with (map (\ aG => ((DOT aG.x (DO gs)), st)) $
                          filter (\ aG => aG.g st) gs)
    _ | [] = [(SKIP, st)]
    _ | ys = ys

  ||| We can convert a GCL program to a transition digram by using the program
  ||| as the state and the operational semantics as the transition function.
  public export
  covering
  gclToDiag : GCL -> Diagram GCL Sts
  gclToDiag p = TD ops p

