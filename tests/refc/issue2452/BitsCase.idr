x : Bits8
x = 0

main : IO ()
main = do
  putStrLn $
    case x of
      0 => "good"
      _ => "bad"
