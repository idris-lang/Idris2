module Libraries.System.Directory.Tree

import Control.Monad.Either
import Data.DPair
import Data.List
import Data.Nat
import System.Directory
import System.File
import Libraries.Utils.Path

%default total

------------------------------------------------------------------------------
-- Filenames

||| A `Filename root` is anchored in `root`.
||| We use a `data` type so that Idris can easily infer `root` when passing
||| a `FileName` around. We do not use a `record` because we do not want to
||| allow users to manufacture their own `FileName`.
||| To get an absolute path, we need to append said filename to the root.
export
data FileName : Path -> Type where
  MkFileName : String -> FileName root

||| Project the string out of a `FileName`.
export
fileName : FileName root -> String
fileName (MkFileName str) = str

namespace FileName
  export
  toRelative : FileName root -> FileName (parse "")
  toRelative (MkFileName x) = MkFileName x

||| Convert a filename anchored in `root` to a filepath by appending the name
||| to the root path.
export
toFilePath : {root : Path} -> FileName root -> String
toFilePath file = show (root /> fileName file)

export
directoryExists : {root : Path} -> FileName root -> IO Bool
directoryExists fp = do
  Right dir <- openDir (toFilePath fp)
    | Left _ => pure False
  closeDir dir
  pure True

------------------------------------------------------------------------------
-- Directory trees

||| A `Tree root` is the representation of a directory tree anchored in `root`.
||| Each directory contains a list of files and a list of subtrees waiting to be
||| explored. The fact these subtrees are IO-bound means the subtrees will be
||| lazily constructed on demand.
public export
SubTree : Path -> Type

public export
record Tree (root : Path) where
  constructor MkTree
  files    : List (FileName root)
  subTrees : List (SubTree root)

SubTree root = (dir : FileName root ** IO (Tree (root /> fileName dir)))

||| An empty tree contains no files and has no sub-directories.
export
emptyTree : Tree root
emptyTree = MkTree [] []

namespace Tree
  ||| No run time information is changed,
  ||| so we assert the identity.
  export
  toRelative : Tree root -> Tree (parse "")
  toRelative x = believe_me x

||| Filter out files and directories that do not satisfy a given predicate.
export
filter : (filePred, dirPred : {root : _} -> FileName root -> Bool) ->
         {root : _} -> Tree root -> Tree root
filter filePred dirPred (MkTree files dirs) = MkTree files' dirs' where

  files' : List (FileName root)
  files' = filter filePred files

  dirs' : List (SubTree root)
  dirs' = flip mapMaybe dirs $ \ (dname ** iot) => do
            guard (dirPred dname)
            pure (dname ** map (assert_total (filter filePred dirPred)) iot)

||| Sort the lists of files and directories using the given comparison functions
export
sortBy : (fileCmp, dirCmp : {root : _} -> FileName root -> FileName root -> Ordering) ->
         {root : _} -> Tree root -> Tree root
sortBy fileCmp dirCmp (MkTree files dirs) = MkTree files' dirs' where

  files' : List (FileName root)
  files' = sortBy fileCmp files

  dirs' : List (SubTree root)
  dirs' = sortBy (\ d1, d2 => dirCmp (fst d1) (fst d2))
        $ flip map dirs $ \ (dname ** iot) =>
          (dname ** map (assert_total (sortBy fileCmp dirCmp)) iot)

||| Sort the list of files and directories alphabetically
export
sort : {root : _} -> Tree root -> Tree root
sort = sortBy cmp cmp where

  cmp : {root : _} -> FileName root -> FileName root -> Ordering
  cmp a b = compare (fileName a) (fileName b)


||| Exploring a filesystem from a given root to produce a tree
export
explore : (root : Path) -> IO (Tree root)

go : {root : Path} -> Directory -> Tree root -> IO (Tree root)

explore root = do
  Right dir <- openDir (show root)
    | Left err => pure emptyTree
  assert_total (go dir emptyTree)

go dir acc = case !(nextDirEntry dir) of
  -- If there is no next entry then we are done and can return the accumulator.
  Left err      => acc <$ closeDir dir
  Right Nothing => acc <$ closeDir dir
  -- Otherwise we have an entry and need to categorise it
  Right (Just entry) => do
    -- ignore aliases for current and parent directories
    let False = elem entry [".", ".."]
         | _ => assert_total (go dir acc)
    -- if the entry is a directory, add it to the (lazily explored)
    -- list of subdirectories
    let entry : FileName root = MkFileName entry
    let acc = if !(directoryExists entry)
                then { subTrees $= ((entry ** explore _) ::) } acc
                else { files    $= (entry                ::) } acc
    assert_total (go dir acc)

||| Depth first traversal of all of the files in a tree
export
covering
depthFirst : ({root : Path} -> FileName root -> Lazy (IO a) -> IO a) ->
             {root : Path} -> Tree root -> IO a -> IO a
depthFirst check t k =
  let next = foldr (\ (dir ** iot), def => depthFirst check !iot def) k t.subTrees in
  foldr (\ fn, def => check fn def) next t.files

||| Display a tree by printing it procedurally. Note that because directory
||| trees contain suspended computations corresponding to their subtrees this
||| has to be an `IO` function. We make it return Unit rather than a String
||| because we do not want to assume that the tree is finite.
export
covering
print : Tree root -> IO ()
print t = go [([], ".", Evidence root (pure t))] where

  -- This implementation is unadulterated black magic.
  -- Do NOT touch it if nothing is broken.

  padding : Bool -> List Bool -> String
  padding isDir = fastConcat . go [] where

    go : List String -> List Bool -> List String
    go acc [] = acc
    go acc (b :: bs) = go (hd :: acc) bs where
      hd : String
      hd = if isDir && isNil acc
           then if b then " ├ " else " └ "
           else if b then " │"  else "  "

  prefixes : Nat -> List Bool
  prefixes n = snoc (replicate (pred n) True) False

  covering
  go : List (List Bool, String, Exists (IO . Tree)) -> IO ()
  go [] = pure ()
  go ((bs, fn, Evidence _ iot) :: iots) = do
    t <- iot
    putStrLn (padding True bs ++ fn)
    let pad = padding False bs
    let pads = prefixes (length t.files + length t.subTrees)
    for_ (zip pads t.files) $ \ (b, fp) =>
      putStrLn (pad ++ (if b then " ├ " else " └ ") ++ fileName fp)
    let bss = map (:: bs) (prefixes (length t.subTrees))
    go (zipWith (\ bs, (dir ** iot) => (bs, fileName dir, Evidence _ iot)) bss t.subTrees)
    go iots

||| Copy a directory and its contents recursively
||| Returns a FileError if the target directory already exists, or if any of
||| the source files fail to be copied.
export
covering
copyDir : HasIO io => (src : Path) -> (target : Path) -> io (Either FileError ())
copyDir src target = runEitherT $ do
    MkEitherT $ createDir $ show target
    copyDirContents !(liftIO $ explore src) target
  where
    copyFile' : (srcDir : Path) -> (targetDir : Path) -> (fileName : String) -> EitherT FileError io ()
    copyFile' srcDir targetDir fileName = do
      MkEitherT $ copyFile (show $ srcDir /> fileName) (show $ targetDir /> fileName)

    covering
    copyDirContents : {srcDir : Path} -> Tree srcDir -> (targetDir : Path) -> EitherT FileError io ()
    copyDirContents (MkTree files subTrees) targetDir = do
      traverse_ (copyFile' srcDir targetDir) (map fileName files)
      traverse_ (\(subDir ** subDirTree) => do
          let targetSubDir = targetDir /> fileName subDir
          MkEitherT $ createDir $ show $ targetSubDir
          copyDirContents !(liftIO subDirTree) targetSubDir
        ) subTrees
