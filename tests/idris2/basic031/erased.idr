data MyMaybe : (0 x : Type) -> Type where
  MyNothing : MyMaybe a
  MyJust : a -> MyMaybe a

-- Should fail since type argument is deleted
nameOf : Type -> String
nameOf (MyMaybe Bool) = "MyMaybe Bool"
nameOf (MyMaybe Int) = "MyMaybe Int"
nameOf _ = "Unknown"

main : IO ()
main = do
  putStrLn (nameOf (MyMaybe Bool))
  putStrLn (nameOf (MyMaybe Int))
  putStrLn (nameOf Int)
