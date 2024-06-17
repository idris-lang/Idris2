import Control.Monad.State
import Data.SnocList

import Language.JSON

jsons : List JSON
jsons = [
    JNull,
    JBoolean False,
    JNumber 1.0,
    JString "Lorem, ipsum",
    JArray [JNull],
    JArray [JBoolean True],
    JObject [],
    JObject [("a", JString "Hello"), ("b", JString "world")],
    JObject [("b", JString "world"), ("a", JString "Hello")]
]

bigJSON : JSON
bigJSON = JObject [
    ("a", JObject [
        ("x", JString "foo"),
        ("y", JString "bar")
    ]),
    ("b", JNull),
    ("c", JString "baz"),
    ("d", JArray [
        JString "qux"
    ])
  ]

main : IO ()
main = do
    for_ jsons $ \json =>
        printLn $ map (== json) jsons

    printLn $ lookup "a" bigJSON
    printLn $ lookup "e" bigJSON
    printLn $ lookup "a" JNull

    let f : Maybe JSON -> Maybe JSON = \case
        Nothing => Just $ JNumber 0
        Just JNull => Just $ JNumber 1
        Just (JString _) => Nothing
        Just json => Just json

    printLn $ update f "a" bigJSON
    printLn $ update f "b" bigJSON
    printLn $ update f "c" bigJSON
    printLn $ update f "e" bigJSON

    printLn $ runState ([<] {a = String}) $ traverseJSON (\case
        JString x => do
            modify (:< x)
            pure $ JString $ x ++ "!"
        json => pure json) bigJSON

    printLn $ execState ([<] {a = String}) $ traverseJSON_ (\case
        JString x => do
            modify (:< x)
        json => pure ()) bigJSON
