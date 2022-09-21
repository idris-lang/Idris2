import Data.List
import Data.Nat

insertAtCases : List (List Nat)
insertAtCases = [
    insertAt 0 9 [6, 7, 8],
    insertAt 1 9 [6, 7, 8],
    insertAt 3 9 [6, 7, 8],
    insertAt 0 9 [6],
    insertAt 1 9 [6],
    insertAt 0 9 []
  ]

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
  printLn insertAtCases
  printLn deleteAtCases
  printLn replaceAtCases
