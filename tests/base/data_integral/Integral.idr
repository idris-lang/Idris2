import Data.Integral
import Data.Nat

Cases : Type
Cases = List Bool

natEvenCases : Cases
natEvenCases = [
    even 0,
    even 2,
    even 4,
    even Z,
    even (S (S Z))
  ]

natOddCases : Cases
natOddCases = [
    odd 1,
    odd 3,
    odd 5,
    odd (S Z),
    odd (S (S (S Z)))
  ]

integralEvenCases : Cases
integralEvenCases = [
    even (-4),
    even (-2),
    even 0,
    even 2,
    even 4
]

integralOddCases : Cases
integralOddCases = [
    odd (-5),
    odd (-3),
    odd (-1),
    odd 1,
    odd 3,
    odd 5
]

main : IO ()
main = do
  printLn "Nat Even"
  printLn natEvenCases
  printLn "Nat Odd"
  printLn natOddCases
  printLn "Integral Even"
  printLn integralEvenCases
  printLn "Integral Odd"
  printLn integralOddCases
