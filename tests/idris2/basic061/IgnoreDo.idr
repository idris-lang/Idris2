module IgnoreDo

bound : Maybe () -> Maybe b -> Maybe b
bound m n = do
  x <- m
  n

ignored : Maybe () -> Maybe b -> Maybe b
ignored m n = do
  _ <- m
  n

seqd : Maybe () -> Maybe b -> Maybe b
seqd m n = do
  m
  n
