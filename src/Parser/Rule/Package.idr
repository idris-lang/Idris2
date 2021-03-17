module Parser.Rule.Package

import public Parser.Lexer.Package
import public Parser.Rule.Common

import Data.List
import Data.List1

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
                      (\x => case x of
                                  Equals => Just ()
                                  _ => Nothing)

export
lte : Rule ()
lte = terminal "Expected <="
                      (\x => case x of
                                  LTE => Just ()
                                  _ => Nothing)

export
gte : Rule ()
gte = terminal "Expected >="
                      (\x => case x of
                                  GTE => Just ()
                                  _ => Nothing)

export
lt : Rule ()
lt = terminal "Expected <="
                      (\x => case x of
                                  LT => Just ()
                                  _ => Nothing)

export
gt : Rule ()
gt = terminal "Expected >="
                      (\x => case x of
                                  GT => Just ()
                                  _ => Nothing)

export
eqop : Rule ()
eqop = terminal "Expected =="
                      (\x => case x of
                                  EqOp => Just ()
                                  _ => Nothing)

export
andop : Rule ()
andop = terminal "Expected &&"
                      (\x => case x of
                                  AndOp => Just ()
                                  _ => Nothing)

export
eoi : Rule ()
eoi = terminal "Expected end of input"
               (\x => case x of
                           EndOfInput => Just ()
                           _ => Nothing)

export
exactProperty : String -> Rule String
exactProperty p = terminal ("Expected property " ++ p)
                           (\x => case x of
                                       DotSepIdent Nothing p' =>
                                         if p == p' then Just p
                                         else Nothing
                                       _ => Nothing)

export
stringLit : Rule String
stringLit = terminal "Expected string"
                     (\x => case x of
                                 StringLit str => Just str
                                 _ => Nothing)

export
integerLit : Rule Integer
integerLit = terminal "Expected integer"
                     (\x => case x of
                                 IntegerLit i => Just i
                                 _ => Nothing)

export
namespacedIdent : Rule (Maybe Namespace, String)
namespacedIdent = terminal "Expected namespaced identifier"
                           (\x => case x of
                                       DotSepIdent ns n => Just (ns, n)
                                       _ => Nothing)

export
moduleIdent : Rule ModuleIdent
moduleIdent = terminal "Expected module identifier"
                       (\x => case x of
                                   DotSepIdent ns m => Just $ nsAsModuleIdent (mkNestedNamespace ns m)
                                   _ => Nothing)

export
packageName : Rule String
packageName = terminal "Expected package name"
                       (\x => case x of
                                   DotSepIdent Nothing str =>
                                     if isIdent AllowDashes str then Just str
                                     else Nothing
                                   _ => Nothing)

export
dot' : Rule ()
dot' = terminal "Expected dot"
                (\x => case x of
                            Dot => Just ()
                            _ => Nothing)

sep' : Rule ()
sep' = terminal "Expected separator"
                (\x => case x of
                            Separator => Just ()
                            _ => Nothing)

export
sep : Rule t -> Rule (List t)
sep rule = forget <$> sepBy1 sep' rule
