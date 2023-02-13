-- We expect the error to occur at a non-empty FC
bar : Maybe Int

foo : Either String Int
foo = do
  Right n <- pure bar | _ => Left "fail"
  pure 42
