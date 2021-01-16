main : IO ()
main = do
  [| (const $ pure MkUnit) (pure ()) |]
  pure ()
