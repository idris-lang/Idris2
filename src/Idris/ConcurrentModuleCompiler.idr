module Idris.ConcurrentModuleCompiler

import Data.Either
import Data.List1
import Data.List
import Data.Strings
import System.Concurrency
import System.File
import Text.Bounded

import Core.Core
import Idris.Parser
import Idris.Pretty
import Idris.ProcessIdr
import Idris.Syntax
import Parser.Lexer.Source
import Parser.Source
import Parser.Support

Show Import where
  show i = show i.path


Show Module where
  show m =
    "Module: " ++ show m.moduleNS ++ "\n" ++
    "----------------------------------------\n" ++
    "Imports: \n" ++
    unlines (show <$> m.imports) ++ "\n"

readFile' : FileName -> Future (FileName, Either Error String)
readFile' file = normalize <$> futureRead
  where
    futureRead : Future (Either FileError String)
    futureRead = forkIO $ do
      putStrLn $ "Reading: " ++ file
      readFile file
    normalize : Either FileError String -> (String, Either Error String)
    normalize content = (file, bimap (FileErr file) id content)

readHeaders' : List FileName -> List FileName -> List (Either Error Module)
readHeaders' _ [] = []
readHeaders' read toRead =
  let futureReadFiles   = readFile' <$> toRead
      futureParsedFiles = map parseHeader <$> futureReadFiles
      awaitedModules = await <$> futureParsedFiles
      imports = concat $ .imports <$> rights awaitedModules
      uniqueImports = nub $ show <$> imports
      newImports = foldl (.) id (delete <$> read) $ uniqueImports
      newImportPaths = ((\p => p ++ ".idr") . fastConcat . intersperse "/" . forget . split (== '.')) <$> newImports
      in awaitedModules ++ readHeaders' (union read toRead) newImportPaths
  where
    isColon : WithBounds Token -> Bool
    isColon t = case t.val of
                     Symbol ":" => True
                     _          => False
    parseHeader : (FileName, Either Error String) -> Either Error Module
    parseHeader (file, content) = do
      c <- content
      let parsed = runParserTo (isLitFile file) isColon c (progHdr file)
      bimap (\err => ParseFail (getParseErrorLoc file err) err) id parsed

readHeaders : List FileName -> List (Either Error Module)
readHeaders toRead = readHeaders' [] toRead


testCase : IO (List Unit)
testCase =
  let printImports = putStrLn <$> show <$> (rights $ readHeaders ["Idris/Main.idr"]) in
  sequence printImports
