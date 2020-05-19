module Main

import Data.Vect

infixr 5 .+.

data Schema = SString | SInt | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore (size : Nat) where
  constructor MkData
  schema : Schema
  items : Vect size (SchemaType schema)

setSchema : DataStore 0 -> Schema -> DataStore 0
setSchema (MkData schema []) schema' = MkData schema' []

data Command : Schema -> Type where
     SetSchema : Schema -> Command schema
     Add : SchemaType schema -> Command schema
     Get : Integer -> Command schema
     Quit : Command schema


