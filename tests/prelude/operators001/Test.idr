
testPipelineRight : Bool
testPipelineRight =
    ([[1], [2], [3]] |> join |> map (* 2)) == [2,4,6]

testPipelineLeft : Bool
testPipelineLeft =
    (unpack <| "hello" ++ "world") == ['h', 'e', 'l', 'l', 'o', 'w', 'o', 'r', 'l', 'd']
