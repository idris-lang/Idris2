module Validation

-- Main purpose of this module is verifying programmer's assumptions about
-- user input. On one hand we want to write precisely typed programs, including
-- assumptions about input expressed in types and prove correctness of these
-- programs. On the other we get an unstructured user input as a string or even
-- a raw sequence of bytes.

-- This module intends to provide a framework for verifying our assumptions
-- about user input and constructing proofs that input is indeed valid or
-- failing early with a nice error message if it isn't.

import Control.Monad.Identity
import Control.Monad.Syntax
import Control.Monad.Trans.Either
import Data.Nat
import Data.Strings
import Data.Vect
import Decidable.Equality

%default total


public export
Result : (Type -> Type) -> Type -> Type
Result m = EitherT m String

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
export
data ValidatorT : (Type -> Type) -> Type -> Type -> Type where
    MkValidator : (a -> Result m b) -> ValidatorT m a b

public export
Validator : Type -> Type -> Type
Validator = ValidatorT Identity


||| Run validation on given input, returning (Right refinedInput) if everything
||| is all right or (Left errorMessage) if it's not.
export
validateT : ValidatorT m a b -> a -> Result m b
validateT (MkValidator v) = v

||| Run validation within the Identity monad and unwrap result immediately.
export
validate : Validator a b -> a -> Either String b
validate v = runIdentity . runEitherT . validateT v

||| Given a function from input to Either String output, make a structural
||| validator.
export
validator : (a -> Result m b) -> ValidatorT m a b
validator = MkValidator

export
Functor m => Functor (ValidatorT m a) where
    map f v = MkValidator (map f . validateT v)

export
Monad m => Applicative (ValidatorT m a) where
    pure a = MkValidator (const $ pure a)
    f <*> a = MkValidator (\x => validateT f x <*> validateT a x)

export
Monad m => Monad (ValidatorT m a) where
    v >>= f = MkValidator $ \x => do
        r <- validateT v x
        validateT (f r) x

replaceError : Monad m => String -> Result m a -> Result m a
replaceError e = bimapEitherT (const e) id

||| Replace validator's default error message.
export
withError : Monad m => String -> ValidatorT m a b -> ValidatorT m a b
withError e (MkValidator f) = MkValidator (replaceError e . f)

||| A validator which always fails with a given message.
export
fail : Applicative m => String -> ValidatorT m a b
fail s = MkValidator $ \_ => fail s

infixl 2 >>>

||| Compose two validators so that the second validates the output of the first.
export
(>>>) : Monad m => ValidatorT m a b -> ValidatorT m b c -> ValidatorT m a c
left >>> right = MkValidator (validateT left >=> validateT right)

Monad m => Alternative (ValidatorT m a) where
    left <|> right = MkValidator \x => MkEitherT $ do
        case !(runEitherT $ validateT left x) of
            (Right r) => pure $ Right r
            (Left e) => case !(runEitherT $ validateT right x) of
                (Right r) => pure $ Right r
                (Left e') => pure $ Left (e <+> " / " <+> e')

||| Alter the input before validation using given function.
export
contramap : (a -> b) -> ValidatorT m b c -> ValidatorT m a c
contramap f v = MkValidator (validateT v . f)


||| Given a value x and a decision procedure for property p, validateT if p x
||| holds, returning a proof if it does. The procedure also has access to the
||| raw input in case it was helpful.
export
decide : Monad m => {0 a, b : Type} -> String -> (x : b) -> {p : b -> Type} -> (a -> (x : b) -> Dec (p x)) -> ValidatorT m a (p x)
decide {a} {b} msg x {p} f = MkValidator $ \a => case f a x of
    Yes prf => pure prf
    No _ => fail msg

||| Given a function converting a into Maybe b, build a Validator of a
||| converting it into b.
export
fromMaybe : Monad m => (a -> String) -> (a -> Maybe b) -> ValidatorT m a b
fromMaybe e f = MkValidator \a => case f a of
    Nothing => fail $ e a
    Just b => pure b

||| Verify whether a String represents a natural number.
export
natural : Monad m => ValidatorT m String Nat
natural = fromMaybe mkError parsePositive
    where
    mkError : String -> String
    mkError s = "'" <+> s <+> "' is not a natural number."

||| Verify whether a String represents an Integer
export
integral : (Num a, Neg a, Monad m) => ValidatorT m String a
integral = fromMaybe mkError parseInteger
    where
    mkError : String -> String
    mkError s = "'" <+> s <+> "' is not an integer."

||| Verify that a string represents a decimal fraction.
export
double : Monad m => ValidatorT m String Double
double = fromMaybe mkError parseDouble
    where
    mkError : String -> String
    mkError s = "'" <+> s <+> "is not a decimal."


||| Verify whether a list has a desired length.
export
length : Monad m => (l : Nat) -> ValidatorT m (List a) (Vect l a)
length l = MkValidator (validateVector l)
    where
    validateVector : (l : Nat) -> List a -> Result m (Vect l a)
    validateVector Z [] = pure []
    validateVector (S _) [] = fail "Missing list element."
    validateVector Z (_ :: _) = fail "Excessive list element."
    validateVector (S k) (x :: xs) = do
        ys <- validateVector k xs
        pure (x :: ys)

||| Verify that certain values are equal.
export
equal : (DecEq a, Monad m) => (x, y : a) -> ValidatorT m z (x = y)
equal x y = MkValidator dec
    where
    dec : z -> Result m (x = y)
    dec _ = case decEq x y of
        Yes prf => pure prf
        No _ => fail "Values are not equal."

||| Verify that a Nat is less than or equal to  certain bound.
export
lteNat : Monad m => {0 a : Type} -> (bound, n : Nat) -> ValidatorT m a (LTE n bound)
lteNat {a} bound n = decide
    (show n <+> " is not lower or equal to " <+> show bound)
    {p = \x => LTE x bound}
    n
    (\_, x => isLTE x bound)

||| Verify that a Nat is greater than or equal to certain bound.
export
gteNat : Monad m => {0 a : Type} -> (bound, n : Nat) -> ValidatorT m a (GTE n bound)
gteNat {a} bound n = lteNat n bound

||| Verify that a Nat is strictly less than a certain bound.
export
ltNat : Monad m => {0 a : Type} -> (bound, n : Nat) -> ValidatorT m a (LT n bound)
ltNat bound n = lteNat bound (S n)

||| Verify that a Nat is strictly greate than a certain bound.
export
gtNat : Monad m => {0 a : Type} -> (bound, n : Nat) -> ValidatorT m a (GT n bound)
gtNat bound n = ltNat n bound
