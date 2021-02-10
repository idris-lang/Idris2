module RecordProjection

record Name where
  constructor MkName
  firstName : String
  lastName : String

(.fullName) : Name -> String
name.fullName = name.firstName ++ " " ++ name.lastName

johnSmith : Name
johnSmith = MkName
  { firstName = "John"
  , lastName = "Smith"
  }

main : IO ()
main = assert_total $ do
  putStrLn johnSmith.firstName
  putStrLn johnSmith.lastName
  putStrLn johnSmith.fullName
