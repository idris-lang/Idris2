module LetInDo

letInDo : Monad m => m Int
letInDo = do
  y <- pure 10
  let x = 5 in pure $ y + x
