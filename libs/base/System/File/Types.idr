module System.File.Types

%default total

||| A pointer to a file.
public export
FilePtr : Type
FilePtr = AnyPtr

||| A file handle.
public export
data File : Type where
     FHandle : FilePtr -> File
