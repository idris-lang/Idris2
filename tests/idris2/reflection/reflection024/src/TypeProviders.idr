||| This module is purely for illustration purposes of the mechanism a-la original type providers
module TypeProviders

import Data.List1

import Language.JSON.Data

import Language.Reflection

%default total

%language ElabReflection

||| Mode one: source of truth in an external file, so generate Idris definitions using a file

declareRecordFromSimpleText : LookupDir -> (path : String) -> (tyName, consName : Name) -> Elab ()
declareRecordFromSimpleText lk textPath dataName consName = do
  let errDesc : Elab String := do pure "text at \{textPath} in \{!(idrisDir lk)}"
  Just text <- readFile lk textPath
    | Nothing => do fail "Did not found \{!errDesc}"
  let fs = lines text
  fs <- for fs $ \line => case words line of
          [name, type] => pure (name, type)
          _ => fail "Expected two strings in line in \{!errDesc}"
  let dataDecl : Decl = IRecord EmptyFC Nothing (specified Public) Nothing $
                          MkRecord EmptyFC dataName [] [] consName $
                            fs <&> \(name, type) => do
                              let (ns, n) = unsnoc $ split (== '.') type
                              let type = if null ns then UN $ Basic n
                                           else NS (MkNS $ reverse ns) (UN $ Basic n)
                              MkIField EmptyFC MW ExplicitArg (UN $ Basic name) (IVar EmptyFC type)
  declare [dataDecl]

-- Declare a type from a definitions in a file
%runElab declareRecordFromSimpleText CurrentModuleDir "fancy-record.txt" `{FancyRecord} `{MkFancyRecord}

-- Use newly created data type
frVal : FancyRecord
frVal = MkFancyRecord {natField = S Z, boolField = True}

||| Mode two: source of truth in Idris module, so generate an external file by Idris definition

saveRecordToSimpleJSON : LookupDir -> (path : String) -> (type : Name) -> Elab ()
saveRecordToSimpleJSON lk jsonPath type = do
  infos <- getInfo type
  let [(type, _)] = flip filter infos $ \case
                      (name, MkNameInfo $ TyCon _ _) => True
                      _                              => False
    | [] => fail "Did not found any type matching \{show type}"
    | (_::_) => fail "Too many types matching \{show type}"
  [con] <- getCons type
    | [] => fail "Did not found any constructors of \{show type}"
    | (_::_) => fail "Too many constructors of \{show type}"
  [(_, conType)] <- getType con
    | _ => fail "Error while getting the type of constructor \{show con}"
  args <- unPi conType
  let args = args <&> map (JString . show)
  writeFile lk jsonPath $ show $ JObject args

  where

    unPi : TTImp -> Elab $ List (String, TTImp)
    unPi $ IPi _ MW ExplicitArg (Just $ UN $ Basic nm) ty rest = ((nm, ty) ::) <$> unPi rest
    unPi $ IPi fc _ _ _ _ _ = failAt fc "Unsupported parameter (we support only omega explicit simply named ones)"
    unPi _ = pure []

-- Declare a type which would be a source of truth
record AnotherFancyRecord where
  veryStringField : String
  veryIntegerField : Integer
  varyNatField : Nat

-- Generate an external description to a data type
%runElab saveRecordToSimpleJSON CurrentModuleDir "another-fancy-record.json" `{AnotherFancyRecord}
