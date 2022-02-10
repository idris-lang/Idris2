import Data.List

deleteAt : List (List Nat)
deleteAt = [
    deleteAt 0 [3],
    deleteAt 0 [3, 4],
    deleteAt 1 [3, 4],
    deleteAt 0 [3, 4, 5],
    deleteAt 1 [3, 4, 5],
    deleteAt 2 [3, 4, 5]
  ]

main : IO ()
main = do printLn takeFromStream
