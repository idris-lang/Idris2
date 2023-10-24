{-------------------------}
-- These should be
-- ignored
{- {---------------} -}

-- Comments should have the right to be empty:
--

-- This is a valid comment {-
-- It should not lead to a parse error if nested in a
-- multiline comment

{- Hence this test

-- This is a valid comment {-
-- It should not lead to a parse error if nested in a
-- multiline comment

-}

myString : String
myString = "Similarly, this is a valid string literal {- "
-- So we should be able to put it in a multiline comment

{- Hence this test

myString : String
myString = "Similarly, this is a valid string literal {- "
-- So we should be able to put it in a multiline comment

-}


{------------- Some people {---- like ---}
  {- comments with
     weird
 ----------}
 closing delimiters
 --}
