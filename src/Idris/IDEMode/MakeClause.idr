module Idris.IDEMode.MakeClause

import Core.Name
import Parser.Lexer.Source
import Parser.Unlit

import Data.List
import Data.Nat
import Data.String

%default total

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
          mkWithPat markerM indent lhs
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

export
makeCase : Bool -> Name -> String -> String
makeCase brack n srcline
    = let capp = ("case _ of", "case_val => ?" ++ show n) in
          newLines capp
  where
    addBrackets : Bool -> String -> String
    addBrackets False str = str
    addBrackets True str = "(" ++ str ++ ")"

    addCase : Nat -> (String, String) -> String
    addCase n (c, pat)
        = addBrackets brack $ c ++ "\n" ++
              pack (replicate (n + (if brack then 6 else 5)) ' ') ++ pat

    replaceStr : Nat -> String -> (String, String) -> String -> String
    replaceStr indent rep new "" = ""
    replaceStr indent rep new str
        = if isPrefixOf rep str
             then addCase indent new ++ pack (drop (length rep) (unpack str))
             else assert_total $ strCons (prim__strHead str)
                          (replaceStr (1 + indent) rep new
                                      (prim__strTail str))

    newLines : (String, String) -> String
    newLines capp = replaceStr 0 ("?" ++ show n) capp srcline
