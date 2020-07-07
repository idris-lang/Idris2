module Data.Either

%default total

||| True if the argument is Left, False otherwise
public export
isLeft : Either a b -> Bool
isLeft (Left _)  = True
isLeft (Right _) = False

||| True if the argument is Right, False otherwise
public export
isRight : Either a b -> Bool
isRight (Left _)  = False
isRight (Right _) = True

||| Keep the payloads of all Left constructors in a list of Eithers
public export
lefts : List (Either a b) -> List a
lefts []              = []
lefts (Left  l :: xs) = l :: lefts xs
lefts (Right _ :: xs) = lefts xs

||| Keep the payloads of all Right constructors in a list of Eithers
public export
rights : List (Either a b) -> List b
rights []              = []
rights (Left  _ :: xs) = rights xs
rights (Right r :: xs) = r :: rights xs

||| Split a list of Eithers into a list of the left elements and a list of the right elements
public export
partitionEithers : List (Either a b) -> (List a, List b)
partitionEithers l = (lefts l, rights l)

||| Remove a "useless" Either by collapsing the case distinction
public export
fromEither : Either a a -> a
fromEither (Left l)  = l
fromEither (Right r) = r

||| Right becomes left and left becomes right
public export
mirror : Either a b -> Either b a
mirror (Left  x) = Right x
mirror (Right x) = Left x

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

||| Convert a Maybe to an Either by using a default value in case of Nothing
||| @ e the default value
public export
maybeToEither : (def : Lazy e) -> Maybe a -> Either e a
maybeToEither def (Just j) = Right j
maybeToEither def Nothing  = Left  def

||| Convert an Either to a Maybe from Right injection
public export
eitherToMaybe : Either e a -> Maybe a
eitherToMaybe (Left _) = Nothing
eitherToMaybe (Right x) = Just x

-- Injectivity of constructors

||| Left is injective
leftInjective : Left x = Left y -> x = y
leftInjective Refl = Refl

||| Right is injective
rightInjective : Right x = Right y -> x = y
rightInjective Refl = Refl
