%default total

tailRecId : (a -> Either a b) -> a -> b
tailRecId f a = case f a of
  Left a2 => tailRecId f a2
  Right b => b

iamvoid : Void
iamvoid = tailRecId go ()
  where go : () -> Either () Void
        go () = Left ()
