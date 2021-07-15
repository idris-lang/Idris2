||| Implementation of ordering relations for the primitive type `Int`
||| This is full of tricks as `Int` is a primitive type that can only
||| be interacted with using either literals or built-in functions.
||| The exported interface should however be safe.
module Data.Int.Order

import Data.Order

%default total

------------------------------------------------------------------------
-- Introduction

-- The type `Int` is a primitive type in Idris. The only handle we have on
-- it is provided by built-in functions. This is what we are going to use
-- to define relations on Int values. For instance, we will declare that
-- `a` is strictly less than `b` whenever `a < b` is provably equal to `True`.

-- These built-in functions only reduce on literals. This means we will not
-- be able to rely on their computational behaviour to prove statements in
-- open contexts.

-- For instance, no amount of pattern-matching will help us prove:
-- LT_not_EQ : LT a b -> Not (EQ a b)

-- Our solution in this file is to use unsafe primitives to manufacture such
-- proofs. This means we are going to essentially postulate some *conditional*
-- results. We do not want such conditional results to reduce to canonical
-- forms too eagerly.

-- Indeed the statement `GT 0 1 -> EQ 0 1` should be provable because 0 is not
-- greater than 1. But its proof should not reduce to a constant function
-- returning the value `Refl` because it is not true that `0` and `1` can be
-- unified. If the proof were to behave this way, we could, in an absurd context,
-- coerce values from any type to any other and cause segmentation faults.

-- Our solution is to be extremely wary of proofs that are passed to us
-- and to only consider returning a magically-crafted output if we have
-- managed to observe that the input is itself in canonical form i.e. to
-- have evaluation stuck on open terms.

-- This is the purpose of the `strictX : X -> Lazy c -> c` functions defined in
-- this file. They all will be waiting until their first argument is in canonical
-- form before returning their second.


------------------------------------------------------------------------
-- Utility functions for equality

||| Pattern-match on an equality proof so that the second argument to
||| strictRefl is only returned once the first is canonical.
export
strictRefl : a === b -> Lazy c -> c
strictRefl Refl p = p

||| Do NOT re-export
unsafeRefl : {0 a, b : t} -> a === b
unsafeRefl = believe_me (the (a === a) Refl)

------------------------------------------------------------------------
-- LT

namespace LT

  ||| `LT a b` is a proof that `a` is less than `b` which is to say that
  ||| the function call `a < b` returns `True`.
  |||
  ||| NB: we do not re-export the constructor so that users cannot force
  ||| our magic functions to blow up in absurd contexts by bypassing the
  ||| safety measures introduced by the `strictX` functions.
  ||| We do provide functions corresponding to the wrapping and unwrapping
  ||| of `LT` but, crucially, they do not let people force `LT` proofs to
  ||| be in canonical form.
  export
  data LT : Int -> Int -> Type where
    MkLT : (a < b) === True -> LT a b

  ||| We may prove `LT a b` by using a proof that `a < b` returns `True`.
  export
  mkLT : (a < b) === True -> LT a b
  mkLT = MkLT

  ||| From a proof that `LT a b`, we may concluded that `a < b` returns `True`.
  export
  runLT : LT a b -> (a < b) === True
  runLT (MkLT eq) = eq

  ||| Do not trust arbitrary `LT` proofs when manufacturing magic ones:
  ||| be strict!
  export
  strictLT : LT a b -> Lazy c -> c
  strictLT (MkLT p) c = strictRefl p c

  ||| LT is decidable, by virtue of being the reflection of a boolean function
  export
  decide : (a, b : Int) -> Dec (LT a b)
  decide a b with (the (test : Bool ** (a < b) === test) (a < b ** Refl))
    decide a b | (True ** p) = Yes (MkLT p)
    decide a b | (False ** p) = No (\ (MkLT q) => absurd (trans (sym p) q))

  ||| LT is a transitive relation. This cannot be proven so we use a magic trick.
  export
  trans : LT a b -> LT b c -> LT a (the Int c)
  trans p q = strictLT p $ strictLT q $ MkLT unsafeRefl

  ||| LT is an irreflexive relation.
  ||| The crash will never happen because the `LT a a` argument will never reduce
  ||| to a canonical form (unless the built-in function (<) is buggy).
  export
  irrefl : Not (LT a a)
  irrefl p = strictLT p
           $ assert_total $ idris_crash "IMPOSSIBLE: LT is irreflexive"

------------------------------------------------------------------------
-- GT

||| GT is defined in terms of LT to avoid code duplication
public export
GT : Int -> Int -> Type
GT = flip LT

export
LT_not_GT : LT a b -> Not (GT a b)
LT_not_GT p q = irrefl (trans p q)

export
GT_not_LT : GT a b -> Not (LT a b)
GT_not_LT = flip LT_not_GT

------------------------------------------------------------------------
-- EQ

namespace EQ

  ||| `EQ a b` is a proof that `a` is equal to `b` which is to say that
  ||| the function call `a == b` returns `True`.
  |||
  ||| NB: we do not re-export the constructor so that users cannot force
  ||| our magic functions to blow up in absurd contexts by bypassing the
  ||| safety measures introduced by the `strictX` functions.
  ||| We do provide functions corresponding to the wrapping and unwrapping
  ||| of `EQ` but, crucially, they do not let people force `EQ` proofs to
  ||| be in canonical form.
  export
  data EQ : Int -> Int -> Type where
    MkEQ : (a == b) === True -> EQ a b

  ||| We may prove `EQ a b` by using a proof that `a == b` returns `True`.
  export
  mkEQ : (a == b) === True -> EQ a b
  mkEQ = MkEQ

  ||| From a proof that `EQ a b`, we may concluded that `a == b` returns `True`.
  export
  runEQ : EQ a b -> (a == b) === True
  runEQ (MkEQ eq) = eq

  ||| Do not trust arbitrary `EQ` proofs when manufacturing magic ones:
  ||| be strict!
  export
  strictEQ : EQ a b -> Lazy c -> c
  strictEQ (MkEQ p) c = strictRefl p c

  ||| EQ is decidable, by virtue of being the reflection of a boolean function
  export
  decide : (a, b : Int) -> Dec (EQ a b)
  decide a b with (the (test : Bool ** (a == b) === test) (a == b ** Refl))
    decide a b | (True  ** p) = Yes (MkEQ p)
    decide a b | (False ** p) = No (\ (MkEQ q) => absurd (trans (sym p) q))

  ||| EQ is a reflexive relation
  export
  refl : EQ a a
  refl = MkEQ unsafeRefl

  ||| EQ is substitutive
  export
  elimEQ : (0 p : Int -> Type) -> EQ a b -> p a -> p b
  elimEQ _ p v = strictEQ p $ believe_me v

  ||| EQ implies propositional equality
  export
  reflect : EQ a b -> a === b
  reflect p = elimEQ (\ b => a === b) p Refl

  ||| EQ is a symmetric relation
  export
  sym : EQ a b -> EQ b a
  sym p = elimEQ (\ b => EQ b a) p refl

  ||| EQ is a transitive relation
  export
  trans : EQ a b -> EQ b c -> EQ a c
  trans p q = elimEQ (\ b => EQ b c) (sym p) q

export
trans_LT_EQ : LT a b -> EQ b c -> LT a c
trans_LT_EQ p q = elimEQ (LT a) q p

export
trans_EQ_LT : EQ a b -> LT b c -> LT a c
trans_EQ_LT p q = elimEQ (\ b => LT b c) (sym p) q

export
LT_not_EQ : LT a b -> Not (EQ a b)
LT_not_EQ p q = irrefl (trans_LT_EQ p (sym q))

export
EQ_not_LT : EQ a b -> Not (LT a b)
EQ_not_LT = flip LT_not_EQ

export
EQ_not_GT : EQ a b -> Not (GT a b)
EQ_not_GT = EQ_not_LT . sym

export
GT_not_EQ : GT a b -> Not (EQ a b)
GT_not_EQ = flip EQ_not_GT

------------------------------------------------------------------------
-- LTE

namespace LTE

  ||| `LTE a b` is a proof that `a` is less or equal to `b` which is to say that
  ||| the function call `a < b` or `a == b` returns `True`.
  |||
  ||| NB: we do not re-export the constructor so that users cannot force
  ||| our magic functions to blow up in absurd contexts by bypassing the
  ||| safety measures introduced by the `strictX` functions.
  export
  data LTE : Int -> Int -> Type where
    MkLT : (a < b)  === True -> LTE a b
    MkEQ : (a == b) === True -> LTE a b

  ||| Unwrap an LTE proof to get either an LT or an EQ one
  export
  runLTE : LTE a b -> Either (LT a b) (EQ a b)
  runLTE (MkLT p) = Left (mkLT p)
  runLTE (MkEQ p) = Right (mkEQ p)

  ||| Do not trust arbitrary `LTE` proofs when manufacturing magic ones:
  ||| be strict!
  export
  strictLTE : LTE a b -> Lazy c -> c
  strictLTE (MkLT p) q = strictRefl p q
  strictLTE (MkEQ p) q = strictRefl p q

  ||| LTE is decidable by virture of both LT and EQ being decidable
  export
  decide : (a, b : Int) -> Dec (LTE a b)
  decide a b with (LT.decide a b)
    decide a b | Yes p = Yes (MkLT (runLT p))
    decide a b | No notLT with (EQ.decide a b)
      decide a b | No notLT | Yes p = Yes (MkEQ (runEQ p))
      decide a b | No notLT | No notEQ = No $ \ case
        MkLT p => notLT (mkLT p)
        MkEQ p => notEQ (mkEQ p)

  ||| LTE is a reflexive relation
  export
  refl : LTE a a
  refl = MkEQ unsafeRefl

  export
  trans_LT_LTE : LT a b -> LTE b c -> LT a c
  trans_LT_LTE p (MkLT q) = trans p (mkLT q)
  trans_LT_LTE p (MkEQ q) = trans_LT_EQ p (mkEQ q)

  export
  trans_LTE_LT : LTE a b -> LT b c -> LT a c
  trans_LTE_LT (MkLT p) q = trans (mkLT p) q
  trans_LTE_LT (MkEQ p) q = trans_EQ_LT (mkEQ p) q

  export
  inject_LT_LTE : LT a b -> LTE a b
  inject_LT_LTE = MkLT . runLT

  export
  inject_EQ_LTE : EQ a b -> LTE a b
  inject_EQ_LTE p = MkEQ (runEQ p)

  ||| LTE is a transitive relation
  export
  trans : LTE a b -> LTE b c -> LTE a c
  trans (MkLT p) q = inject_LT_LTE (trans_LT_LTE (mkLT p) q)
  trans p (MkLT q) = inject_LT_LTE (trans_LTE_LT p (mkLT q))
  trans (MkEQ p) (MkEQ q) = inject_EQ_LTE (trans (mkEQ p) (mkEQ q))

  ||| LTE is an antisymmetric relation
  export
  antisym : LTE a b -> LTE b a -> EQ a b
  antisym (MkEQ p) _ = mkEQ p
  antisym _ (MkEQ p) = EQ.sym (mkEQ p)
  antisym (MkLT p) (MkLT q) = absurd $ LT.irrefl (LT.trans (mkLT p) (mkLT q))

------------------------------------------------------------------------
-- GTE

||| GTE is defined in terms of LTE to avoid code duplication
public export
GTE : Int -> Int -> Type
GTE = flip LTE

------------------------------------------------------------------------
-- Trichotomy and other decidability results

||| Any pair of Ints is related either via LT, EQ, or GT
export
trichotomous : (a, b : Int) -> Trichotomous LT EQ GT a b
trichotomous a b with (LTE.decide a b)
  trichotomous a b | Yes lte = case runLTE lte of
    Left lt  => MkLT lt (LT_not_EQ lt) (LT_not_GT lt)
    Right eq => MkEQ (EQ_not_LT eq) eq (EQ_not_GT eq)
  trichotomous a b | No notLTE = let gt = mkLT unsafeRefl in MkGT (GT_not_LT gt) (GT_not_EQ gt) gt

||| Any pair of Ints is related either via LT or GTE
export
decide_LT_GTE : (a, b : Int) -> Either (LT a b) (GTE a b)
decide_LT_GTE a b with (trichotomous a b)
  decide_LT_GTE a b | MkLT lt _ _ = Left lt
  decide_LT_GTE a b | MkEQ _ eq _ = Right (inject_EQ_LTE (sym eq))
  decide_LT_GTE a b | MkGT _ _ gt = Right (inject_LT_LTE gt)

||| Any pair of Ints is related either via LTE or GT
export
decide_LTE_GT : (a, b : Int) -> Either (LTE a b) (GT a b)
decide_LTE_GT a b with (trichotomous a b)
  decide_LTE_GT a b | MkLT lt _ _ = Left (inject_LT_LTE lt)
  decide_LTE_GT a b | MkEQ _ eq _ = Left (inject_EQ_LTE eq)
  decide_LTE_GT a b | MkGT _ _ gt = Right gt

------------------------------------------------------------------------
-- Some properties

||| Adding one to a strictly smaller Int, yields a smaller Int
export
suc_LT_LTE : {a, b : Int} -> LT a b -> LTE (a + 1) b
suc_LT_LTE p with (the (test : Bool ** (a + 1 == b) === test) (a + 1 == b ** Refl))
  suc_LT_LTE p | (True  ** q) = inject_EQ_LTE $ mkEQ q
  suc_LT_LTE p | (False ** q) = strictLT p $ inject_LT_LTE $ mkLT unsafeRefl

||| Subtracting one to a strictly larger Int, yields a larger Int
export
pred_LT_LTE : {a, b : Int} -> LT a b -> LTE a (b - 1)
pred_LT_LTE p with (the (test : Bool ** (a == b - 1) === test) (a == b - 1 ** Refl))
  pred_LT_LTE p | (True  ** q) = inject_EQ_LTE $ mkEQ q
  pred_LT_LTE p | (False ** q) = strictLT p $ inject_LT_LTE $ mkLT unsafeRefl

||| Adding one to an Int yields a strictly larger one,
||| provided there is no overflow
export
sucBounded : LT a b -> LT a (a + 1)
sucBounded p = strictLT p $ mkLT unsafeRefl
