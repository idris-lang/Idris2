module Libraries.Data.SnocList.LengthMatch

%default total

public export
data LengthMatch : SnocList a -> SnocList b -> Type where
     LinMatch : LengthMatch [<] [<]
     SnocMatch : LengthMatch xs ys -> LengthMatch (xs :< x) (ys :< y)

export
checkLengthMatch : (xs : SnocList a) -> (ys : SnocList b) ->
  Maybe (LengthMatch xs ys)
checkLengthMatch [<] [<] = Just LinMatch
checkLengthMatch [<] (_ :< _) = Nothing
checkLengthMatch (_ :< _) [<] = Nothing
checkLengthMatch (xs :< _) (ys :< _)
    = Just (SnocMatch !(checkLengthMatch xs ys))

export
lengthsMatch : LengthMatch xs ys -> (length xs) = (length ys)
lengthsMatch LinMatch = Refl
lengthsMatch (SnocMatch x) = cong S (lengthsMatch x)

export
reverseOnto : LengthMatch sx sy -> LengthMatch sx' sy' ->
  LengthMatch (reverseOnto sx sx') (reverseOnto sy sy')
reverseOnto p LinMatch = p
reverseOnto p (SnocMatch x) = reverseOnto (SnocMatch p) x

export
reverse : LengthMatch sx sy -> LengthMatch (reverse sx) (reverse sy)
reverse = reverseOnto LinMatch
