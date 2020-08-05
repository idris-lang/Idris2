module Data.Either.Extra

import Data.List1

%default total

export
getLeft : Either a b -> Maybe a
getLeft (Left v) = Just v
getLeft _ = Nothing

export
getRight : Either a b -> Maybe b
getRight (Right v) = Just v
getRight _ = Nothing

mutual

  ||| `group` compresses the list of Lefts and Rights by accumulating
  ||| all of the lefts and rights into blocks.
  export
  group : List (Either a b) -> List (Either (List1 a) (List1 b))
  group []               = []
  group (Left a :: abs)  = lefts  [a] abs
  group (Right b :: abs) = rights [b] abs

  lefts : List1 a -> List (Either a b) -> List (Either (List1 a) (List1 b))
  lefts acc (Left a :: abs) = lefts (cons a acc) abs
  lefts acc abs             = Left (reverse acc) :: group abs

  rights : List1 b -> List (Either a b) -> List (Either (List1 a) (List1 b))
  rights acc (Right b :: abs) = rights (cons b acc) abs
  rights acc abs              = Right (reverse acc) :: group abs

||| `ungroup` is the inverse of `group` (the converse is not true as nothing
||| forces the input to be maximally grouped!)
export
ungroup : List (Either (List1 a) (List1 b)) -> List (Either a b)
ungroup = concatMap $ \ abs => case abs of
  Left as  => map Left  $ List1.toList as
  Right bs => map Right $ List1.toList bs

export
pushInto : c -> Either a b -> Either (c, a) (c, b)
pushInto c (Left a)  = Left (c, a)
pushInto c (Right b) = Right (c, b)
