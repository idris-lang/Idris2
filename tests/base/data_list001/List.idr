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

main : IO ()
main = do printLn deleteAtCases
