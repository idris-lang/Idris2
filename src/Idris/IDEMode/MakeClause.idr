module Idris.IDEMode.MakeClause

import Core.Name
import Parser.Lexer
import Parser.Unlit

import Data.List
import Data.Nat
import Data.Strings

-- Implement make-with and make-case from the IDE mode

showRHSName : Name -> String
showRHSName n
    = let fn = show (dropNS n) in
          if any isOpChar (unpack fn)
             then "op"
             else fn

export
makeWith : Name -> String -> String
makeWith n srcline
    = let (markerM, src) = isLitLine srcline
          isrc : (Nat, String) =
             case span isSpace src of
                  (spc, rest) => (length spc, rest)
          indent = fst isrc
          src = snd isrc
          lhs = pack (readLHS 0 (unpack src)) in
          mkWithArg markerM indent lhs ++ "\n" ++
          mkWithPat markerM indent lhs ++ "\n"
  where
    readLHS : (brackets : Nat) -> List Char -> List Char
    readLHS Z ('=' :: rest) = []
    readLHS n ('(' :: rest) = '(' :: readLHS (S n) rest
    readLHS n ('{' :: rest) = '{' :: readLHS (S n) rest
    readLHS n (')' :: rest) = ')' :: readLHS (pred n) rest
    readLHS n ('}' :: rest) = '}' :: readLHS (pred n) rest
    readLHS n (x :: rest) = x :: readLHS n rest
    readLHS n [] = []

    pref : Maybe String -> Nat -> String
    pref mark ind = relit mark $ pack (replicate ind ' ')

    mkWithArg : Maybe String -> Nat -> String -> String
    mkWithArg mark indent lhs
        = pref mark indent ++ lhs ++ "with (_)"

    mkWithPat : Maybe String -> Nat -> String -> String
    mkWithPat mark indent lhs
        = pref mark (indent + 2) ++ lhs ++ "| with_pat = ?" ++
              showRHSName n ++ "_rhs"
