allLengths : List String -> List Nat
allLengths [] = []
allLengths (word :: words) = length word :: allLengths words
