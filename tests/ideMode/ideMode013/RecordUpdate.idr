module RecordUpdate

record Attributes where
  font : String
  size : Nat

bigMono : Attributes -> Attributes
bigMono = { font $= (++ "Mono")
          , size := 20
          }

smallMono : Attributes -> Attributes
smallMono = { size := 5 } . bigMono

-- Works for nested too
record Text where
  attributes : Attributes
  content : String

setArial10 : Text -> Text
setArial10 = { attributes->font := "Arial"
             , attributes.size := 10
             }
