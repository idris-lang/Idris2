module Module'

function' : Int -> Int
function' x = x + 1

main : IO ()
main = printLn $ function' 4
