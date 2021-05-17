module Main

test_string : String
test_string = "1234567890"

main : IO()
main = assert_total $ do
    putStrLn $ show $ length test_string
