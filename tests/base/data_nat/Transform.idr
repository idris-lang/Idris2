
import Data.Nat


showLTE : LTE n m -> String
showLTE LTEZero  = "LTEZero"
showLTE (LTESucc y) = "LTESucc " ++ show (believe_me{b=Nat} y)

main : IO ()
main = do
  let n : Nat = 10000000
  putStrLn (case isLTE 0 (S n) of
                 Yes x => showLTE x
                 No _ => "No")
  putStrLn (case isLTE n (S n) of
                 Yes x => showLTE x
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

