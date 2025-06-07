import Language.Reflection

%language ElabReflection

minusList : TTImp -> List TTImp -> TTImp
minusList x [] = x
minusList x (y :: ys) =
  IApp EmptyFC ( IApp EmptyFC `( (-) ) x ) y `minusList` ys

%macro
minusLocals : Elab Int
minusLocals = do
  vars <- localVars
  case map (\y => IVar EmptyFC y) vars of
    []        => pure 0
    (x :: xs) => check $ minusList x xs

minusTwo : Int -> Int -> Int -> Int
minusTwo x y z = minusLocals

minusFive : (x, y1, y2, y3, y4, y5 : Int) -> Int
minusFive x y1 y2 y3 y4 y5 = minusLocals

main : IO ()
main = do
  printLn $ minusTwo 1 2 3
  printLn $ minusFive 1 2 3 4 5 6
