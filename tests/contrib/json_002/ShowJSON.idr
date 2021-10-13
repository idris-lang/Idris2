import Language.JSON

someJSON : JSON
someJSON = JObject [
    ("a", JNull),
    ("b", JBoolean True),
    ("c", JNumber 1),
    ("d", JString "Hello, world"),
    ("e", JArray [JNull, JString "Lorem ipsum"]),
    ("f", JObject [("key", JString "value")])
  ]

main : IO ()
main = do
    putStrLn $ show someJSON
    putStrLn $ show @{Idris} someJSON
    putStrLn $ format 4 someJSON
