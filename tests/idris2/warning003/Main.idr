module Main

record TestRecord where
  constructor MkTestRecord
  recField : Int

testRec : TestRecord
testRec = MkTestRecord 0

updatedRec : TestRecord
updatedRec = record { recField = 1 } testRec
