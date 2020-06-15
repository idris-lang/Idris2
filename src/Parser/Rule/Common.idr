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
         pure (tok.line, tok.col)

export
endLocation : {token : _} -> EmptyRule token (Int, Int)
endLocation
    = do tok <- peek
         pure (tok.endLine, tok.endCol)

export
position : {token : _} -> EmptyRule token ((Int, Int), (Int, Int))
position
    = do tok <- peek
         pure ((tok.line, tok.col), (tok.endLine, tok.endCol))


export
column : {token : _ } -> EmptyRule token Int
column
    = do (line, col) <- location
         pure col
