module Language.Reflection.Disambiguate

import public Data.List
import public Data.List1
import public Data.String

import Language.Reflection

%language ElabReflection

||| Given a namespace filter, represented as a dotted string,
||| and a (partial) name - tries to disambiguate
||| the latter among the set of all full names,
||| compatible with it.
||| Returns the one matching name, or fails
||| if multiple or none fit the filter.
export
pickName : String -> Name -> Elab Name
pickName filterStr n = do
  let infixNS = reverse $ forget (split (== '.') filterStr)
  names <- getType n
  let [one] = filter (f infixNS) (map fst names)
   | [] => fail "No name matches the query"
   | many => fail $ "Multiple names match the query: "
       ++ show many
  pure one
 where
  f : List String -> Name -> Bool
  f infixNS (NS (MkNS ns) name) = isInfixOf infixNS ns
  f _ _ = False

||| Same as above, but hides the selected name instead.
export
hideName : String -> Name -> Elab ()
hideName filter name = do
  one <- pickName filter name
  declare [IHide EmptyFC one]
