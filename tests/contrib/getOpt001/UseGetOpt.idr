module UseGetOpt

import Data.DPair
import Data.So

import Deriving.Show

import System
import System.Console.GetOpt

%default total

%language ElabReflection

data Command = Up | Down | Left | Right

%hint ShowCommand : Show Command; ShowCommand = %runElab derive

record Config where
  constructor MkConfig
  fieldA : Maybe Bits64
  fieldB : Integer
  fieldC : String
  fieldD : SnocList String
  fieldE : Bool
  fieldF : Bool
  commands : SnocList Command

%hint ShowConfig : Show Config; ShowConfig = %runElab derive

defaultConfig : Config
defaultConfig = MkConfig
  { fieldA = Nothing
  , fieldB = -1
  , fieldC = ""
  , fieldD = [<]
  , fieldE = False
  , fieldF = False
  , commands = [<]
  }

parseFieldA : String -> Either String $ Config -> Config
parseFieldA str = case parsePositive str of
                    Just n  => Right { fieldA := Just n }
                    Nothing => Left "Cannot parse field A with `\{str}`"

parseFieldB : String -> Either String $ Config -> Config
parseFieldB str = case parseInteger str of
                    Just n  => Right { fieldB := n }
                    Nothing => Left "Cannot parse field B with `\{str}`"

parseFieldE : Maybe String -> Either String $ Config -> Config
parseFieldE Nothing        = Right { fieldE := True }
parseFieldE (Just "true")  = Right { fieldE := True }
parseFieldE (Just "false") = Right { fieldE := False }
parseFieldE (Just str)     = Left "Unknown boolean value `\{str}`"

parseCommand : String -> Either String $ Config -> Config
parseCommand "up"    = Right { commands $= (:< Up) }
parseCommand "down"  = Right { commands $= (:< Down) }
parseCommand "left"  = Right { commands $= (:< Left) }
parseCommand "right" = Right { commands $= (:< Right) }
parseCommand cmd     = Left "Unknown command `\{cmd}`"

cliOpts : List $ OptDescr $ Config -> Config
cliOpts =
  [ MkOpt [] ["field-a"]
      (ReqArg' parseFieldA "<bits-64>")
      "Sets the value of the field A"
  , MkOpt ['b'] ["field-b"]
      (ReqArg' parseFieldB "<integer>")
      "Sets the value of the field B"
  , MkOpt ['c'] ["field-c"]
      (ReqArg (\s => the (Config -> Config) { fieldC := s }) "<string>")
      "Sets the value of the field C"
  , MkOpt ['d'] ["field-d"]
      (ReqArg (\s => the (Config -> Config) { fieldD $= (:< s) }) "<string>")
      "Adds a string to the value of the field D"
  , MkOpt ['e'] ["field-e"]
      (OptArg' parseFieldE "<bool>")
      "Sets (by default), or resets the flag of field E"
  , MkOpt ['f'] ["field-f"]
      (NoArg $ the (Config -> Config) { fieldF := True })
      "Sets the flag of field F"
  ]

printList : (name : String) -> List String -> IO ()
printList name [] = putStrLn "\{name}: none"
printList name lst = do
  putStrLn "\{name}:"
  for_ lst $ putStrLn . ("  - " ++)

main : IO ()
main = do
  putStrLn "----------"
--  let usage : Lazy String := usageInfo "\nUsage:" cliOpts
  args <- fromMaybe [] . tail' <$> getArgs
  putStrLn "raw args: \{show args}"
  let result = getOpt (ReturnInOrder' parseCommand) cliOpts args
  let conf = foldl (flip (.)) id result.options $ defaultConfig
  printList "non-options" result.nonOptions
  printList "unrecognised" result.unrecognized
  printList "errors" result.errors
  putStrLn "config: \{show conf}"
