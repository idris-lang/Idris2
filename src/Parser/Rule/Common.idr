module Parser.Rule.Common

import public Text.Lexer
import public Text.Parser

%default total

public export
Rule : Type -> Type -> Type
Rule token ty = Grammar (TokenData token) True ty

public export
EmptyRule : Type -> Type -> Type
EmptyRule token ty = Grammar (TokenData token) False ty

export
location : {token : _} -> EmptyRule token (Int, Int)
location
    = do tok <- peek
         pure (line tok, col tok)

export
column : {token : _ } -> EmptyRule token Int
column
    = do (line, col) <- location
         pure col
