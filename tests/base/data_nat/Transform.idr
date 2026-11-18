
import Data.Nat

main : IO ()
main = do
  let n : Nat = 10000000
  putStrLn (case isLTE n (S n) of
                 Yes _ => "Yes"
                 No _ => "No")
  putStrLn (case isLTE (S n) n of
                 Yes _ => "Yes"
                 No _ => "No")
  putStrLn $ show $ lte n (S n)
  putStrLn $ show $ lte (S n) n
  putStrLn $ show $ minimum (S n) n
  putStrLn $ show $ minimum n (S n)
  putStrLn $ show $ maximum (S n) n
  putStrLn $ show $ maximum n (S n)

