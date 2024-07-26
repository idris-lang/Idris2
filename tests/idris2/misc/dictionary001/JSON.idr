
-- JSON DLS
namespace Map
  public export
  data StrMap : Type -> Type where
    DNil : StrMap a
    DCons : String -> a -> StrMap a -> StrMap a

data JSON = Object (StrMap JSON) | Array (List JSON) | Number Double | Str String

DCons : String -> JSON -> StrMap JSON -> JSON
DCons key val m = Object (DCons key val m)

(::) : JSON -> List JSON -> JSON
(::) x xs = Array (x :: xs)

Nil : JSON
Nil = Array []

DNil : JSON
DNil = Object DNil

fromString : String -> JSON
fromString = Str

fromInteger : Integer -> JSON
fromInteger = Number . cast

fromDouble : Double -> JSON
fromDouble = Number

-- Building JSON Values

testEmptyArray : JSON
testEmptyArray = []

testEmptyObj : JSON
testEmptyObj = [:=]

testObject : JSON
testObject = [ "hello" := "world"
             , "key2" := "value2"
             ]

testNested : JSON
testNested =
  [ "key1" := 3
  , "key2" := "hello"
  , "key3" := [1, 2, "hello"]
  , "key4" := [ "nestedKey1" := "nestedVal1"
              , "nestedKey2" := [ "nestedArray1", "nestedArray2" ]
              ]
  , "key4" :=
    [ "Nestedkey3" :=
      [ "NestedKey4" := [:=]
      , "NestedKey5" :=
        [ "NestedKey6" := "vlue"
        , "NestedKey7" := []
        ]
      ]
    , "NestedKey8" := 5
    ]
  ]

