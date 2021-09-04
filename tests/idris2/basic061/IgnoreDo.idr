module IgnoreDo

bound : Maybe () -> Maybe b -> Maybe b
bound m n = do
  x <- m
  let y = Z
  n

ignored : Maybe () -> Maybe b -> Maybe b
ignored m n = do
  _ <- m
  let _ = Z
  n

seqd : Maybe () -> Maybe b -> Maybe b
seqd m n = do
  m
  n
