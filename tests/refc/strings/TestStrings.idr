module TestStrings

import Data.String
import Data.String.Iterator

iteratorTail : String -> String
iteratorTail str = withString str $ \it => unconsTail str (uncons str it)
  where
    unconsTail : (str : String) -> (1 _ : UnconsResult str) -> String
    unconsTail str EOF = ""
    unconsTail str (Character _ tailIt) = withIteratorString str tailIt id

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

    let chars = the (List Char) ['a', 'A', '~', '0', ' ', '\n', '\x9f']
    putStrLn $ show $ map isUpper chars
    putStrLn $ show $ map isLower chars
    putStrLn $ show $ map isDigit chars
    putStrLn $ show $ map isSpace chars
    putStrLn $ show $ map isNL chars
    putStrLn $ show $ map isControl chars

    putStrLn $ show $ map {f = List} chr [97, 65, 126, 48, 32, 10, 159]
    putStrLn $ show $ map ord chars

    putStrLn $ show $ Data.String.Iterator.unpack "iterator unpack"
    putStrLn $ show $ iteratorTail "iterator tail"
