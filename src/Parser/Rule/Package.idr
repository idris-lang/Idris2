module Parser.Rule.Package

import public Parser.Lexer.Package
import public Parser.Rule.Common

import Data.List
import Data.List1

%default total

public export
Rule : Type -> Type
Rule = Rule Token

public export
PackageEmptyRule : Type -> Type
PackageEmptyRule = EmptyRule Token

export
equals : Rule ()
equals = terminal "Expected equals"
                      (\x => case tok x of
                                  Equals => Just ()
                                  _ => Nothing)

export
eoi : Rule ()
eoi = terminal "Expected end of input"
               (\x => case tok x of
                           EndOfInput => Just ()
                           _ => Nothing)

export
exactProperty : String -> Rule String
exactProperty p = terminal ("Expected property " ++ p)
                           (\x => case tok x of
                                       DotSepIdent [p'] =>
                                         if p == p' then Just p
                                         else Nothing
                                       _ => Nothing)

export
stringLit : Rule String
stringLit = terminal "Expected string"
                     (\x => case tok x of
                                 StringLit str => Just str
                                 _ => Nothing)

export
namespacedIdent : Rule (List1 String)
namespacedIdent = terminal "Expected namespaced identifier"
                           (\x => case tok x of
                                       DotSepIdent nsid => Just $ reverse nsid
                                       _ => Nothing)

export
moduleIdent : Rule (List1 String)
moduleIdent = terminal "Expected module identifier"
                       (\x => case tok x of
                                   DotSepIdent m => Just $ reverse m
                                   _ => Nothing)

export
packageName : Rule String
packageName = terminal "Expected package name"
                       (\x => case tok x of
                                   DotSepIdent [str] =>
                                     if isIdent AllowDashes str then Just str
                                     else Nothing
                                   _ => Nothing)

sep' : Rule ()
sep' = terminal "Expected separator"
                (\x => case tok x of
                            Separator => Just ()
                            _ => Nothing)

export
sep : Rule t -> Rule (List t)
sep rule = sepBy1 sep' rule
