module Control.Validation

-- Main purpose of this module is verifying programmer's assumptions about
-- user input. On one hand we want to write precisely typed programs, including
-- assumptions about input expressed in types and prove correctness of these
-- programs. On the other we get an unstructured user input as a string or even
-- a raw sequence of bytes.

-- This module intends to provide a framework for verifying our assumptions
-- about user input and constructing proofs that input is indeed valid or
-- failing early with a nice error message if it isn't.

import Control.Monad.Syntax
import Data.Nat
import Data.Strings
import Data.Vect
import Decidable.Equality

%default total


public export
Result : Type -> Type
Result = Either String

||| Validators in this module come in two flavours: Structural Validators and
||| Property Validators. They are both wrappers around functions which take
||| some input and confirm that it's valid (returning some witness of its
||| validity) or fail with an error described by a string.
|||
||| Structural Validators work by refining the type of input, for instance
||| checking whether a string encodes a number and returning that number if it
||| does. More generally, they convert raw input to some more restricted type.
|||
||| Property Validators try to prove that (usually already refined) input has
||| some property and return the proof if it does.
public export
data Validator : Type -> Type -> Type where
    StructValidator : (a -> Result b) -> Validator a b
    PropValidator : {0 a, b : Type} -> {0 p : b -> Type} -> {0 x : b} -> (a -> Result (p x)) -> Validator a (p x)


unwrap : Validator a b -> a -> Result b
unwrap (StructValidator f) = f
unwrap (PropValidator f) = f

export
Functor (Validator a) where
    map f v = StructValidator (map f . unwrap v)

export
Applicative (Validator a) where
    pure a = StructValidator (const $ pure a)
    f <*> a = StructValidator (\x => unwrap f x <*> unwrap a x)

export
Monad (Validator a) where
    v >>= f = StructValidator $ \x => do
        r <- unwrap v x
        unwrap (f r) x

||| Run validation on given input, returning (Right refinedInput) if everything
||| is all right or (Left errorMessage) if it's not.
export
validate : Validator a b -> a -> Result b
validate (StructValidator v) = v
validate (PropValidator v) = v

replaceError : String -> Result a -> Result a
replaceError e (Left _) = Left e
replaceError _ (Right x) = Right x

||| Replace validator's default error message.
export
withError : String -> Validator a b -> Validator a b
withError e (StructValidator f) = StructValidator (replaceError e . f)
withError e (PropValidator {p} {x} f) = PropValidator {p} {x} (replaceError e . f)

||| A validator which always fails with a given message.
export
fail : String -> Validator a b
fail s = StructValidator $ \_ => Left s

infixl 2 >>>

||| Compose two validators so that the second validates the output of the first.
export
(>>>) : Validator a b -> Validator b c -> Validator a c
left >>> right = StructValidator (unwrap left >=> unwrap right)

Alternative (Validator a) where
    left <|> right = StructValidator \x =>
        case unwrap left x of
            Right b => pure b
            Left e => case unwrap right x of
                Right b => pure b
                Left e' => Left (e <+> " / " <+> e')

||| Alter the input before validation using given function.
export
contramap : (a -> b) -> Validator b c -> Validator a c
contramap f v = StructValidator (unwrap v . f)


||| Given a value x and a decision procedure for property p, validate if p x
||| holds, returning a proof if it does. The procedure also has access to the
||| raw input in case it was helpful.
export
decide : {0 a, b : Type} -> String -> (x : b) -> {p : b -> Type} -> (a -> (x : b) -> Dec (p x)) -> Validator a (p x)
decide {a} {b} msg x {p} f = PropValidator {p} {x} $ \a => case f a x of
    Yes prf => Right prf
    No _ => Left msg

||| Given a function converting a into Maybe b, build a Validator of a
||| converting it into b.
export
fromMaybe : (a -> String) -> (a -> Maybe b) -> Validator a b
fromMaybe e f = StructValidator \a => case f a of
    Nothing => Left $ e a
    Just b => Right b

||| Verify whether a String represents a natural number.
export
natural : Validator String Nat
natural = fromMaybe mkError parsePositive
    where
    mkError : String -> String
    mkError s = "'" <+> s <+> "' is not a natural number."

||| Verify whether a String represents an Integer
export
integral : (Num a, Neg a) => Validator String a
integral = fromMaybe mkError parseInteger
    where
    mkError : String -> String
    mkError s = "'" <+> s <+> "' is not an integer."

||| Verify that a string represents a decimal fraction.
export
double : Validator String Double
double = fromMaybe mkError parseDouble
    where
    mkError : String -> String
    mkError s = "'" <+> s <+> "is not a decimal."


||| Verify whether a list has a desired length.
export
length : (l : Nat) -> Validator (List a) (Vect l a)
length l = StructValidator (validateVector l)
    where
    validateVector : (l : Nat) -> List a -> Result (Vect l a)
    validateVector Z [] = Right []
    validateVector (S _) [] = Left "Missing list element."
    validateVector Z (_ :: _) = Left "Excessive list element."
    validateVector (S k) (x :: xs) = do
        ys <- validateVector k xs
        pure (x :: ys)

||| Verify that certain values are equal.
export
equal : DecEq a => (x, y : a) -> Validator z (x = y)
equal x y = PropValidator {p = \z => fst z = snd z} {x = (x, y)} dec
    where
    dec : z -> Result (x = y)
    dec _ = case decEq x y of
        Yes prf => Right prf
        No _ => Left "Values are not equal."

||| Verify that a Nat is less than or equal to  certain bound.
export
lteNat : {0 a : Type} -> (bound, n : Nat) -> Validator a (LTE n bound)
lteNat {a} bound n = decide
    (show n <+> " is not lower or equal to " <+> show bound)
    {p = \x => LTE x bound}
    n
    (\_, x => isLTE x bound)

||| Verify that a Nat is greater than or equal to certain bound.
export
gteNat : {0 a : Type} -> (bound, n : Nat) -> Validator a (GTE n bound)
gteNat {a} bound n = lteNat n bound

||| Verify that a Nat is strictly less than a certain bound.
export
ltNat : {0 a : Type} -> (bound, n : Nat) -> Validator a (LT n bound)
ltNat bound n = lteNat bound (S n)

||| Verify that a Nat is strictly greate than a certain bound.
export
gtNat : {0 a : Type} -> (bound, n : Nat) -> Validator a (GT n bound)
gtNat bound n = ltNat n bound
