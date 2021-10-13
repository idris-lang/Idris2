import Language.JSON

main : IO ()
main = do
    printLn $ JObject [
        ("a", cast ()),
        ("b", cast True),
        ("c", cast 1.0),
        ("d", cast "Hello, world"),
        ("e", cast ["Lorem", "ipsum"])
      ]
