module System.File.Types

%default total

public export
FilePtr : Type
FilePtr = AnyPtr

public export
data File : Type where
     FHandle : FilePtr -> File
