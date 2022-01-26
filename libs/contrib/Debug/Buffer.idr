module Debug.Buffer

import Data.Buffer
import Data.List
import Data.String

toHex : Int -> Int -> String
toHex d n = pack $ reverse $ foldl toHexDigit [] (slice d n [])
    where
        toHexDigit : List Char ->Int -> List Char
        toHexDigit acc i = chr (if i < 10 then i + ord '0' else (i-10) + ord 'A')::acc
        slice : Int -> Int -> List Int -> List Int
        slice 0 _ acc = acc
        slice d n acc = slice (d-1) (n `div` 16) ((n `mod` 16)::acc)

showSep : String -> Nat -> List String -> String
showSep sep _ [] = ""
showSep sep n [x] = x ++ replicate (3*n) ' '
showSep sep Z (x :: xs) = x ++ sep ++ showSep sep Z xs
showSep sep (S n) (x :: xs) = x ++ sep ++ showSep sep n xs

renderRow : List Int -> String
renderRow dat =  showSep " " 16 (map (toHex 2) dat) ++
                "      " ++ pack (map (\i => if i > 0x1f && i < 0x80 then chr i else '.') dat)

group : Nat -> List a -> List (List a)
group n xs = worker [] xs
    where
        worker : List (List a) -> List a -> List (List a)
        worker acc [] = reverse acc
        worker acc ys = worker ((take n ys)::acc) (drop n ys)

export
dumpBuffer : HasIO io => Buffer -> io String
dumpBuffer buf = do
    size <- liftIO $ rawSize buf
    dat <- liftIO $ bufferData buf
    let rows = group 16 dat
    let hex = showSep "\n" 0 (map renderRow rows)
    pure $ hex ++ "\n\ntotal size = " ++ show size

export
printBuffer : HasIO io => Buffer -> io ()
printBuffer buf = putStrLn $ !(dumpBuffer buf)
