-- IfMuliWay should not interfere with normal ifs
barf : Int
barf = if True then 1 else 0

normalIf : Int -> Char
normalIf i = if i + 3 == 7 then '7'
               else if i < 0 then 'N'
                 else 'X'

total
multiNormal : Int -> Char
multiNormal i = if | i + 3 == 7 => '7'
                   | i < 0 => 'N'
                   | _ => 'X'

total
multiOkayIndenation : Int -> Char
multiOkayIndenation i = if | i + 3       == 7  => '7'
                           | i      == 0
                            => '0'
                           | i < 0
                            =>
                            'N'
                           | _ => 'X'

{-
-- Some constant True, IfMuliWay should (be able to) consider this as True
-- but will not since we don't do compile-time evaluation of our cases yet.
-- TODO look into how functions are reduced in types and use those
-- rules to allow reduction for multi-if cases. `otherwise` is vacuously total
-- and there's no reason to not reduce it to True, and also to check that at
-- least one case of a multi-if is _ or True
otherwise : Bool
otherwise = True

-- We don't use this yet, but maybe some day!
-- In fact with proper checking even `otherwise` would be unneccesary here,
-- since our cases cover all possibilities of Int.
total
constTest : Int -> Char
constTest i = if | i > 0 => 'P'
                 | i == 0 => 'Z'
                 | i < 0 => 'N'
                 | otherwise = 'X'
-}

-- Should emit a warning about unreachable cases as 'X' and 'Z' are unreachable
earlyStop : Int -> Char
earlyStop i = if | i > 10 => '7'
                 | _ => '0'
                 | i == 2 => 'X'
                 | _ => 'Z'

-- Using multi anywhere an expression is allowed
arbitraryExpressionPosition1 : Char -> String
arbitraryExpressionPosition1 c = "abc" ++ (if | c == 'a' => "A"
                                              | _ => "z") ++ "def"

-- Using multi anywhere an expression is allowed. Also testing `;`.
-- We're using a block so we don't say `if | i == Z => Bool | _ => Char`
-- Partly because that's how blocks work and partly because we're just asking
-- for syntax clashes if we use | as the sole delimiter.
arbitraryExpressionPosition2 : (i : Nat)
                            -> if | i == Z => Bool; | _ => Char
arbitraryExpressionPosition2 0 = True
arbitraryExpressionPosition2 (S k) = 'F'


partial -- Should be accepted as partial.
partialTest : Int -> Char
partialTest i = if | i + 3 == 7 => '7'
                   | i == 0 => '0'
                   | i < 0 => 'N'

total -- Should not be accepted as total. It's an error so test this last.
partialTest2 : Int -> Char
partialTest2 i = if | i + 3 == 7 => '7'
                    | i == 0 => '0'
                    | i < 0 => 'N'
