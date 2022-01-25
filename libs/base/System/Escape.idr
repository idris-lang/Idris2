module System.Escape

import Data.List

import System.Info

||| Escape special characters in an Idris string, for use as a string literal
||| in the shell
public export
escapeArg : String -> String
escapeArg cmd = let escapedCmdChars = pack $ unpack cmd >>= escapeArgChar in
    if isWindows
       then escapedCmdChars
       else "\"" ++ escapedCmdChars ++ "\""
  where
    escapeArgChar : Char -> List Char
    escapeArgChar c =
        if isWindows
           then if c == '%'  || c == '^'  || c == '&'  || c == '<'  || c == '>' || c == '|' ||
                   c == '\'' || c == '"'  || c == '`'  ||
                   c == ' '  || c == '\t' || c == '\n' || c == ';' || c == ',' || c == '=' || c == '\x0B' || c == '\x0C' || c == '\xFF' ||
                   c == '('  || c == ')'  || c == '!'
                   then ['^', c]
                   else [c]
           else if c == '$' || c == '`' || c == '\\' || c == '"'
                   then ['\\', c]
                   else [c]

||| Escape special characters in a list of shell arguments, as a single command
||| for the shell.
||| eg. the list ["a", "b", "c d"] is interpreted as the command `a b "c d"`
public export
escapeCmd : List String -> String
escapeCmd cmd = concat $ intersperse " " $ map escapeArg cmd
