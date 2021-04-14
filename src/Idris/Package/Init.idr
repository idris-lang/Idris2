module Idris.Package.Init

import Core.FC
import Core.Name.Namespace

import Data.List
import Data.Maybe
import Data.Strings

import Idris.Package.Types
import System.Directory

import Libraries.Utils.Path
import Libraries.System.Directory.Tree
import Libraries.Text.PrettyPrint.Prettyprinter

%default total

isModuleIdent : String -> Bool
isModuleIdent str = case unpack str of
  [] => False
  cs@(hd :: _) => isUpper hd && all isAlphaNum cs

packageTree : (root : Path) -> IO (Tree root)
packageTree root = filter validFile validDirectory <$> explore root where

  validFile : {root : _} -> FileName root -> Bool
  validFile f
    = let (fname, fext) = splitFileName (fileName f) in
      isModuleIdent fname && elem fext ["idr", "lidr"]

  validDirectory : {root : _} -> FileName root -> Bool
  validDirectory = isModuleIdent . fileName

covering
findModules : (start : Maybe String) -> IO (List (ModuleIdent, String))
findModules start = do
  let prfx = fromMaybe "" start
  Just dir <- maybe currentDir (pure . Just) start
    | Nothing => pure []
  let root = parse dir
  tree <- packageTree root
  mods <- go [] [([], (root ** pure tree))]
  pure (sortBy (\ a, b => compare (snd a) (snd b)) mods)

  where

    go : List (ModuleIdent, String) ->
         List (List String, (root : Path ** IO (Tree root))) ->
         IO (List (ModuleIdent, String))
    go acc [] = pure acc
    go acc ((path, (root ** iot)) :: iots) = do
      t <- liftIO iot
      let mods = flip map t.files $ \ entry =>
                   let fname = fst (splitFileName (fileName entry)) in
                   let mod = unsafeFoldModuleIdent (fname :: path) in
                   let fp  = toFilePath entry in
                   (mod, fp)
      let dirs = flip map t.subTrees $ \ (dir ** iot) =>
                   (fileName dir :: path, (_ ** iot))
      go (mods ++ acc) (dirs ++ iots)

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
