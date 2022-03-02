import Data.List

deleteAtCases : List (List Nat)
deleteAtCases = [
    deleteAt 0 [3],
    deleteAt 0 [3, 4],
    deleteAt 1 [3, 4],
    deleteAt 0 [3, 4, 5],
    deleteAt 1 [3, 4, 5],
    deleteAt 2 [3, 4, 5]
  ]

replaceAtCases : List (List Nat)
replaceAtCases = [
    replaceAt 0 6 [3],
    replaceAt 0 6 [3, 4],
    replaceAt 1 6 [3, 4],
    replaceAt 0 6 [3, 4, 5],
    replaceAt 1 6 [3, 4, 5],
    replaceAt 2 6 [3, 4, 5]
  ]

main : IO ()
main = do
  printLn deleteAtCases
  printLn replaceAtCases
