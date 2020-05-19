describe_list_end : List Int -> String
describe_list_end [] = "Empty"
describe_list_end (xs ++ [x]) = "Non-empty, initial portion = " ++ show xs
