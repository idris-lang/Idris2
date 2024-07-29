module Idris.Package.Init

import Core.FC
import Core.Name.Namespace
import Core.Directory

import Data.List
import Data.Maybe
import Data.String

import Idris.Package.Types
import System.Directory
import Control.App.FileIO

import Libraries.Text.Lexer
import Libraries.Utils.Path
import Libraries.System.Directory.Tree

%default total

isModuleIdent : String -> Bool
isModuleIdent str = case unpack str of
  [] => False
  cs@(hd :: _) => isUpper hd && all isAlphaNum cs

packageTree : (root : Path) -> IO (Tree root)
packageTree root = filter validFile validDirectory <$> explore root where

  validFile : {root : _} -> FileName root -> Bool
  validFile f
    = case splitIdrisFileName (fileName f) of
        Nothing => False
        Just (fname, fext) => isModuleIdent fname

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
                   let fname = fst (splitExtensions (fileName entry)) in
                   let mod = unsafeFoldModuleIdent (fname :: path) in
                   let fp  = toFilePath entry in
                   (mod, fp)
      let dirs = flip map t.subTrees $ \ (dir ** iot) =>
                   (fileName dir :: path, (_ ** iot))
      go (mods ++ acc) (dirs ++ iots)

prompt : String -> IO String
prompt p = putStr p >> fflush stdout >> getLine

export
covering
interactive : IO (Maybe PkgDesc)
interactive = do
  pname <- prompt "Package name: "
  let True = checkPackageName $ fastUnpack pname
    | False => pure Nothing
  pauthors <- prompt "Package authors: "
  poptions <- prompt "Package options: "
  psource  <- prompt "Source directory: "
  let sourcedir = mstring psource
  modules  <- findModules sourcedir
  let pkg : PkgDesc =
        { authors   := mstring pauthors
        , options   := (emptyFC,) <$> mstring poptions
        , modules   := modules
        , sourcedir := sourcedir
        } (initPkgDesc (fromMaybe "project" (mstring pname)))
  pure $ Just pkg

  where

    mstring : String -> Maybe String
    mstring str = case trim str of
      "" => Nothing
      str => Just str

    isIdentStart : Char -> Bool
    isIdentStart '_' = True
    isIdentStart x   = isUpper x ||
                       isAlpha x ||
                       x > chr 160

    isIdentTrailing : List Char -> Bool
    isIdentTrailing []      = True
    isIdentTrailing (x::xs) = case isAlphaNum x ||
                                   x > chr 160  ||
                                   x == '-'     ||
                                   x == '_'     ||
                                   x == '\'' of
                                False => False
                                True  => isIdentTrailing xs

    checkPackageName : List Char -> Bool
    checkPackageName []      = True
    checkPackageName (x::xs) = isIdentStart x &&
                               isIdentTrailing xs
