
import Data.Nat

main : IO ()
main = do
  let n : Nat = 10000000
  putStrLn (case isLTE n (S n) of
                 Yes _ => "Yes"
                 No _ => "No")
  putStrLn (case lte n (S n) of
                 True => "True"
                 False => "False")
  putStrLn $ show $ (minimum (S n) n)
  putStrLn $ show $ (maximum (S n) n)

