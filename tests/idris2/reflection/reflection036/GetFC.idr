import Language.Reflection

%language ElabReflection

%macro
here : Elab String
here = do
  MkFC (PhysicalIdrSrc _) (l, c) _ <- getFC
    | _ => fail "expected a physical source location"
  pure $ "line " ++ show l ++ ", col " ++ show c

main : IO ()
main = putStrLn here
