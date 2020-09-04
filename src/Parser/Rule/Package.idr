module Parser.Rule.Package

import public Parser.Lexer.Package
import public Parser.Rule.Common

import Data.List

import Core.Name.Namespace

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
                      (\x => case x.val of
                                  Equals => Just ()
                                  _ => Nothing)

export
eoi : Rule ()
eoi = terminal "Expected end of input"
               (\x => case x.val of
                           EndOfInput => Just ()
                           _ => Nothing)

export
exactProperty : String -> Rule String
exactProperty p = terminal ("Expected property " ++ p)
                           (\x => case x.val of
                                       DotSepIdent Nothing p' =>
                                         if p == p' then Just p
                                         else Nothing
                                       _ => Nothing)

export
stringLit : Rule String
stringLit = terminal "Expected string"
                     (\x => case x.val of
                                 StringLit str => Just str
                                 _ => Nothing)

export
namespacedIdent : Rule (Maybe Namespace, String)
namespacedIdent = terminal "Expected namespaced identifier"
                           (\x => case x.val of
                                       DotSepIdent ns n => Just (ns, n)
                                       _ => Nothing)

export
moduleIdent : Rule ModuleIdent
moduleIdent = terminal "Expected module identifier"
                       (\x => case x.val of
                                   DotSepIdent ns m => Just $ nsAsModuleIdent (mkNestedNamespace ns m)
                                   _ => Nothing)

export
packageName : Rule String
packageName = terminal "Expected package name"
                       (\x => case x.val of
                                   DotSepIdent Nothing str =>
                                     if isIdent AllowDashes str then Just str
                                     else Nothing
                                   _ => Nothing)

sep' : Rule ()
sep' = terminal "Expected separator"
                (\x => case x.val of
                            Separator => Just ()
                            _ => Nothing)

export
sep : Rule t -> Rule (List t)
sep rule = sepBy1 sep' rule
