module Idris.Package.Init

import Core.FC
import Core.Name.Namespace

import Data.List
import Data.Maybe
import Data.Strings

import Idris.Package.Types
import System.Directory

import Libraries.Utils.Path
import Libraries.Text.PrettyPrint.Prettyprinter

%default total

export
covering
interactive : IO PkgDesc
interactive = do
  pname    <- putStr "Package name: " *> getLine
  pauthors <- putStr "Package authors: " *> getLine
  poptions <- putStr "Package options: " *> getLine
  modules  <- findModules
  let pkg : PkgDesc =
        { authors := mstring pauthors
        , options := (emptyFC,) <$> mstring poptions
        , modules := modules
        } (initPkgDesc (fromMaybe "project" (mstring pname)))
  pure pkg

  where
    mstring : String -> Maybe String
    mstring str = case trim str of
      "" => Nothing
      str => Just str

    isModuleIdent : String -> Bool
    isModuleIdent str = case unpack str of
      [] => False
      cs@(hd :: _) => isUpper hd || all isAlphaNum cs

    directoryExists : String -> IO Bool
    directoryExists fp = do
      Right dir <- openDir fp
        | Left _ => pure False
      closeDir dir
      pure True

    PathedName : Type
    PathedName = (List String, String)

    nextDirectory : List PathedName ->
                    IO (Maybe ((List String, Directory), List PathedName))
    nextDirectory [] = pure Nothing
    nextDirectory ((p, d) :: stack) =
      do Right dir <- openDir (foldl (flip (</>)) d p)
            | Left _ => nextDirectory stack -- should be impossible
         pure (Just ((d :: p, dir), stack))

    -- TODO: refactor via an abstract view of the filesystem
    covering
    explore : List (ModuleIdent, String) -> List PathedName ->
              (List String, Directory) -> IO (List (ModuleIdent, String))
    explore acc stack dir@(path, d) = case !(dirEntry d) of
      Left err => do
        -- We're done: move on to the next directory, if there are
        -- none sort the accumulator and return the result
        closeDir d
        case !(nextDirectory stack) of
          Nothing => pure (sortBy (compare `on` snd) acc)
          Just (dir, stack) => explore acc stack dir
      Right entry => do
        -- ignore aliases for current and parent directories
        let False = elem entry [".", ".."]
             | _ => explore acc stack dir
        -- if the entry is a directory, push it on the stack of work to do
        False <- directoryExists (foldl (flip (</>)) entry path)
             | _ => explore acc ((path, entry) :: stack) dir
        -- otherwise make sure it's an idris file
        let (fname, fext) = splitFileName entry
        let True = (fext == "idr" || fext == "lidr") && isModuleIdent fname
             | _ => explore acc stack dir
        -- finally add the file to the accumulator
        let mod = unsafeFoldModuleIdent (fname :: path)
        let fp  = foldl (flip (</>)) fname path
        explore ((mod, fp) :: acc) stack dir

    covering
    findModules : IO (List (ModuleIdent, String))
    findModules = do
      Just curr <- currentDir
        | Nothing => pure []
      Right dir <- openDir curr
        | Left err => pure []
      explore [] [] ([], dir)
