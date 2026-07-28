import Data.String

main : IO ()
main = do
  putStrLn $ show $
    [ parseDouble "+123.123e-2"
    , parseDouble " -123.123E+2"
    , parseDouble " +123.123"
    , parseDouble " 0.123 "
    , parseDouble " -0.123"
    ]


