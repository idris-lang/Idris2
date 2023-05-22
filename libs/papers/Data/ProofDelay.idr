||| The contents of this module are based on the paper
||| Deferring the Details and Deriving Programs
||| by Liam O'Connor
||| https://doi.org/10.1145/3331554.3342605
module Data.ProofDelay

import Data.Nat
import Data.List.Quantifiers

%default total

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
later : {tx : _} -> PDelay tx
later = Prf (tx :: []) (\(x :: []) => x)

-- pronounced "apply"
||| We can compose `PDelay` computations.
public export
(<*>) : PDelay (a -> b) -> PDelay a -> PDelay b
(Prf goals1 prove1) <*> (Prf goals2 prove2) =
  Prf (goals1 ++ goals2) $ \hl =>
    let (left , right) = splitAt _ hl in
    prove1 left (prove2 right)


------------------------------------------------------------------------
-- Example uses

||| An ordered list type.
|||
||| [27](https://dl.acm.org/doi/10.1145/2503778.2503786)
public export
data OList : (m, n : Nat) -> Type where
  Nil  : (m `LTE` n) -> OList m n
  Cons : (x : Nat) -> (m `LTE` x) -> OList x n -> OList m n

||| A binary search tree carrying proofs of the ordering in the leaves.
|||
||| [31](https://dl.acm.org/doi/10.1145/2628136.2628163)
public export
data BST : (m, n : Nat) -> Type where
  Leaf : (m `LTE` n) -> BST m n
  Branch : (x : Nat) -> (l : BST m x) -> (r : BST x n) -> BST m n

-- OList

||| OList `Nil`, but delaying the proof obligation.
public export
nil : {m, n : Nat} -> PDelay (OList m n)
nil = [| Nil later |]

||| OList `Cons`, but delaying the proof obligations.
public export
cons : {m, n : Nat} -> (x : Nat) -> PDelay (OList x n) -> PDelay (OList m n)
cons x xs =
  let cx : ?  -- Idris can figure out the type
      cx = Cons x
  in [| cx later xs |]

||| Extracting an actual `OList` from the delayed version requires providing the
||| unergonomic proofs.
public export
example : OList 1 5
example =
  let structure : ?
      structure = 1 `cons` (2 `cons` (3 `cons` (4 `cons` (5 `cons` nil))))

      proofs : HList ?
      proofs =  LTESucc LTEZero
             :: LTESucc LTEZero
             :: LTESucc (LTESucc LTEZero)
             :: LTESucc (LTESucc (LTESucc LTEZero))
             :: LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))
             :: LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))
             :: []

  in structure.prove proofs

-- BST

||| BST `Leaf`, but delaying the proof obligation.
public export
leaf : {m, n : Nat} -> PDelay (BST m n)
leaf = [| Leaf later |]

||| BST `Branch`, but delaying the proof obligations.
public export
branch :  {m, n : Nat}
       -> (x : Nat)
       -> (l : PDelay (BST m x))
       -> (r : PDelay (BST x n))
       -> PDelay (BST m n)
branch x l r =
  let bx : ?
      bx = Branch x
  in [| bx l r |]

||| Once again, extracting the actual `BST` requires providing the uninteresting
||| proofs.
public export
example2 : BST 2 10
example2 =
  let structure : ?
      structure = branch 3
                    (branch 2 leaf leaf)
                    (branch 5
                      (branch 4 leaf leaf)
                      (branch 10 leaf leaf))

      -- we _could_ construct the proofs by hand, but Idris can just also find
      -- them (as long as we tell it which proof to find)
      proofs : HList ?
      proofs =  the ( 2 `LTE`  2) %search
             :: the ( 2 `LTE`  3) %search
             :: the ( 3 `LTE`  4) %search
             :: the ( 4 `LTE`  5) %search
             :: the ( 5 `LTE` 10) %search
             :: the (10 `LTE` 10) %search
             :: []
      {- proofs =  LTESucc (LTESucc LTEZero)
       -        :: LTESucc (LTESucc LTEZero)
       -        :: LTESucc (LTESucc (LTESucc LTEZero))
       -        :: LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))
       -        :: LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))
       -        :: LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc
       -                   (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))))))))
       -        :: []
       -}

  in structure.prove proofs
