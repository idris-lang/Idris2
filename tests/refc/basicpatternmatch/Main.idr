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
  printLn $ map (\case
                -128 => "-128"
                -127 => "-127"
                0 => "zero"
                127 => "127"
                x => "?" ++ show x
                ) $ [ the Int8 (-128), -127, 0, 127 ]
  printLn $ map (\case
                -128 => "-128"
                -127 => "-127"
                0 => "zero"
                127 => "127"
                255 => "255"
                256 => "256"
                x => "?" ++ show x
                ) $ [ the Bits8 0, 127, 255, 256, 257 ]
  printLn $ map (\case
                -32768 => "-32768"
                0 => "zero"
                32767 => "32767"
                x => "?" ++ show x
                ) $ [ the Int16 (-32768), 0, 32767, 11 ]
  printLn $ map (\case
                32768 => "32768"
                0 => "zero"
                32767 => "32767"
                0xffff => "65535"
                0xff => "255" -- 0x100ff hits this
                x => "?" ++ show x
                ) $ [ the Bits16 32768, 0, 0xffff, 0x100ff ]
  printLn $ map (\case
                -2147483648 => "-2147483648"
                0 => "zero"
                0x7fffffff => "0x7fffffff"
                x => "?" ++ show x
                ) $ [ the Int32 (-2147483648), 0, 0x7fffffff, -1 ]
  printLn $ map (\case
                0x80000000  => "0x80000000"
                21474834648 => "21474834648"
                0 => "zero"
                x => "?" ++ show x
                ) $ [ the Bits32 0x80000000, 0 ]
  printLn $ map (\case
                0 => "zero"
                711 => "711"
                -9223372036854775808 => "-9223372036854775808" -- FIXME: wont work
                9223372036854775807 => "9223372036854775807" -- FIXME: wont work
                x => "?" ++ show x
                ) $ [ the Int64 (-9223372036854775808), 0, 9223372036854775807, 711, 712 ]
  printLn $ map (\case
                0xffffffffffffffff  => "0xffffffffffffffff"
                0 => "zero"
                32768 => "32678"
                x => "?" ++ show x
                ) $ [ the Bits64 0xffffffffffffffff, 0, 32768 ]



  --
  printLn $ map show [D0, D1 99, D2, D3]
  pure ()


