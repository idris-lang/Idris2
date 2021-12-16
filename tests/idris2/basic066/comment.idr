{--- -}
fun : Int -> Bool
fun x = (x /= 0)
{-
-}
main : IO ()
main = print (fun 5)

-- EXPLANATION:
-- this is about parsing the opening `{---`
-- which used to be parsed as two separate tokens `{-` and `--`
-- making the above program fail
