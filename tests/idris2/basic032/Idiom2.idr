-- Things like  ( , )  ( ** )  ()   are special in that they denote more than
-- one thing at once. () can mean Unit or MkUnit, (,) can mean Pair or MkPair
-- Idiom brackets need to be able to work despite that, which is tested here

fez : IO Int
fez = pure 1

fez1 : IO (Int, ())
fez1 = [| MkPair fez (pure ()) |]

fez2 : IO (Int, Maybe Int)
fez2 = [| ( fez , (pure Nothing) ) |]
