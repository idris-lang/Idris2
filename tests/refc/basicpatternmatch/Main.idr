module Main

import Data.Maybe

bw : Type -> Maybe Bits8
bw Bits8 = Just 8
bw Bits16 = Just 16
bw Int8 = Just 8
bw String = Nothing
bw Char = Just 8
bw _ = Nothing

data D = D0 | D1 Int | D2 | D3
Show D where
  show D0 = "D0"
  show (D1 n) = "D1 \{show n}"
  show D2 = "D2"
  show _ = "???"


main : IO ()
main = do
  printLn $ map bw [Int8,  Bits16, Char, String, Integer, (), Nat]
  --
  printLn $ map (\case
      "ABCDE" => "U"
      "abcde" => "L"
      "" => "empty"
      "abcde\0fg" => "1st\02nd"  -- Issue 3161
      _ => "ZZZ") $ the (List String) ["", "ABCDE", "AA", "abcde", "abcde\0fg"]
  --
  printLn $ map (\case
      1.0 => "1.0"
      2.2 => "2.2"
      _ => "?") $ the (List Double) [0.1, 0.2, 1.1, 1.0, 2.0, 2.1, 2.2 ]
  --
  printLn $ pack $ map (\case
      'a' => 'A'
      'b' => 'b'
      'c' => 'C'
      _ => '?') $ unpack "abcdefg"
  --
  printLn $ map show [D0, D1 99, D2, D3]
  pure ()


