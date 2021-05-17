module TestStrings

import Data.String

main : IO ()
main = do
    let helloWorld = "Hello, " ++ "world"

    putStrLn helloWorld
    putStrLn $ show $ length helloWorld

    putStrLn $ reverse helloWorld
    putStrLn $ substr 1 2 helloWorld
    putStrLn $ show $ assert_total $ strIndex helloWorld 1

    putStrLn $ strCons 'a' "bc"
    putStrLn $ show $ strUncons "abc"

    putStrLn $ fastPack ['p', 'a', 'c', 'k']
    putStrLn $ show $ fastUnpack "unpack"
    putStrLn $ fastConcat ["con", "cat", "en", "ate"]

    let chars = ['a', 'A', '~', '0', ' ', '\n', '\x9f']
    putStrLn $ show $ map isUpper chars
    putStrLn $ show $ map isLower chars
    putStrLn $ show $ map isDigit chars
    putStrLn $ show $ map isSpace chars
    putStrLn $ show $ map isNL chars
    putStrLn $ show $ map isControl chars

    putStrLn $ show $ map chr [97, 65, 126, 48, 32, 10, 159]
    putStrLn $ show $ map ord chars
