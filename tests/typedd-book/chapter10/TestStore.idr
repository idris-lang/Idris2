import DataStore

testStore : DataStore (SString .+. SString .+. SInt)
testStore = addToStore ("Mercury", "Mariner 10", 1974) $
            addToStore ("Venus", "Venera", 1961) $
            addToStore ("Uranus", "Voyager 2", 1986) $
            addToStore ("Pluto", "New Horizons", 2015) $
            empty

listItems : DataStore schema -> List (SchemaType schema)
listItems input with (storeView input)
  listItems DataStore.empty | SNil = []
  listItems (addToStore entry store) | (SAdd entry store rec)
         = entry :: listItems store | rec

filterKeys : (test : SchemaType val_schema -> Bool) ->
             DataStore (SString .+. val_schema) -> List String
filterKeys test input with (storeView input)
  filterKeys test DataStore.empty | SNil = []
  filterKeys test (addToStore (key, value) store) | (SAdd (key, value) store rec)
       = if test value
            then key :: filterKeys test store | rec
            else filterKeys test store | rec

