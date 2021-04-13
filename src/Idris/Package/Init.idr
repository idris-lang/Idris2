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
  psource  <- putStr "Source directory: " *> getLine
  let sourcedir = mstring psource
  modules  <- findModules sourcedir
  let pkg : PkgDesc =
        { authors   := mstring pauthors
        , options   := (emptyFC,) <$> mstring poptions
        , modules   := modules
        , sourcedir := sourcedir
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
      cs@(hd :: _) => isUpper hd && all isAlphaNum cs

    directoryExists : String -> IO Bool
    directoryExists fp = do
      Right dir <- openDir fp
        | Left _ => pure False
      closeDir dir
      pure True

    PathedName : Type
    PathedName = (List String, String)

    nextDirectory : String -> List PathedName ->
                    IO (Maybe ((List String, Directory), List PathedName))
    nextDirectory prfx [] = pure Nothing
    nextDirectory prfx ((p, d) :: stack) =
      do Right dir <- openDir (prfx </> foldl (flip (</>)) d p)
            | Left _ => nextDirectory prfx stack -- should be impossible
         pure (Just ((d :: p, dir), stack))

    -- TODO: refactor via an abstract view of the filesystem
    covering
    explore : String ->
              List (ModuleIdent, String) -> List PathedName ->
              (List String, Directory) -> IO (List (ModuleIdent, String))
    explore prfx acc stack dir@(path, d) = case !(dirEntry d) of
      Left err => do
        -- We're done: move on to the next directory, if there are
        -- none sort the accumulator and return the result
        closeDir d
        case !(nextDirectory prfx stack) of
          Nothing => pure (sortBy (\ a, b => compare (snd a) (snd b)) acc)
          Just (dir, stack) => explore prfx acc stack dir
      Right entry => do
        -- ignore aliases for current and parent directories
        let False = elem entry [".", ".."]
             | _ => explore prfx acc stack dir
        -- if the entry is a directory and it is a valid ident,
        -- push it on the stack of work to do
        False <- directoryExists (prfx </> foldl (flip (</>)) entry path)
             | _ => if isModuleIdent entry
                      then explore prfx acc ((path, entry) :: stack) dir
                      else explore prfx acc stack dir
        -- otherwise make sure it's an idris file
        let (fname, fext) = splitFileName entry
        let True = fext == "idr" || fext == "lidr"
             | _ => explore prfx acc stack dir
        -- finally add the file to the accumulator
        let mod = unsafeFoldModuleIdent (fname :: path)
        let fp  = prfx </> foldl (flip (</>)) fname path
        explore prfx ((mod, fp) :: acc) stack dir

    covering
    findModules : Maybe String -> IO (List (ModuleIdent, String))
    findModules sdir = do
      let prfx = fromMaybe "" sdir
      Just curr <- maybe currentDir (pure . Just) sdir
        | Nothing => pure []
      Right dir <- openDir curr
        | Left err => pure []
      explore prfx [] [] ([], dir)
