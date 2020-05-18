module Data.Either

||| True if the argument is Left, False otherwise
public export
isLeft : Either a b -> Bool
isLeft (Left l)  = True
isLeft (Right r) = False

||| True if the argument is Right, False otherwise
public export
isRight : Either a b -> Bool
isRight (Left l)  = False
isRight (Right r) = True

||| Keep the payloads of all Left constructors in a list of Eithers
public export
lefts : List (Either a b) -> List a
lefts []      = []
lefts (x::xs) =
  case x of
    Left  l => l :: lefts xs
    Right r => lefts xs

||| Keep the payloads of all Right constructors in a list of Eithers
public export
rights : List (Either a b) -> List b
rights []      = []
rights (x::xs) =
  case x of
    Left  l => rights xs
    Right r => r :: rights xs

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
total
leftInjective : {b : Type}
             -> {x : a}
             -> {y : a}
             -> (Left {b = b} x = Left {b = b} y) -> (x = y)
leftInjective Refl = Refl

||| Right is injective
total
rightInjective : {a : Type}
              -> {x : b}
              -> {y : b}
              -> (Right {a = a} x = Right {a = a} y) -> (x = y)
rightInjective Refl = Refl
