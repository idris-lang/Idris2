module TestStrings

import Data.String
import Data.String.Iterator

iteratorTail : String -> String
iteratorTail str = withString str $ \it => unconsTail str (uncons str it)
  where
    unconsTail : (str : String) -> (1 _ : UnconsResult str) -> String
    unconsTail str EOF = ""
    unconsTail str (Character _ tailIt) = withIteratorString str tailIt id

isUnderscore : Char -> Bool
isUnderscore '_' = True
isUnderscore _ = False

isHelloWorld : String -> Bool
isHelloWorld "Hello, world" = True
isHelloWorld _ = False

main : IO ()
main = do
    let helloWorld = "Hello, " ++ "world"

    putStrLn helloWorld
    putStrLn $ show $ length helloWorld
    putStrLn $ show $ String.length ""

    putStrLn $ reverse helloWorld
    putStrLn $ reverse ""
    putStrLn $ substr 1 2 helloWorld

    let overtake0 = substr 10 10 helloWorld
    putStrLn $ "\{show $ length overtake0} : \{overtake0}"
    let overtake1 = substr 1 2 ""
    putStrLn $ "\{show $ length overtake1} : \{overtake1}"
    putStrLn $ substr (-10) (1) helloWorld
    putStrLn $ substr 2 (-2) helloWorld
    putStrLn $ substr (-5) (-2) helloWorld
    putStrLn $ substr 1000000 1 helloWorld
    putStrLn $ substr 5 100000 helloWorld

    putStrLn $ show $ assert_total $ strIndex helloWorld 1

    putStrLn $ strCons 'a' "bc"
    putStrLn $ strCons 'a' ""
    putStrLn $ show $ strUncons "abc"
    putStrLn $ show $ strUncons ""

    putStrLn $ fastPack ['p', 'a', 'c', 'k']
    putStrLn $ fastPack []
    putStrLn $ show $ fastUnpack "unpack"
    putStrLn $ show $ fastUnpack ""
    putStrLn $ fastConcat ["con", "cat", "en", "ate"]
    putStrLn $ fastConcat []

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

    -- Test Char pattern matching
    putStrLn $ show $ isUnderscore '_'
    putStrLn $ show $ isUnderscore ' '

    -- Test String pattern matching
    putStrLn $ show $ isHelloWorld helloWorld
    putStrLn $ show $ isHelloWorld "Hello, Idris"
