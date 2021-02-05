module Parser.Rule.Common

import public Libraries.Text.Lexer
import public Libraries.Text.Parser

%default total

public export
Rule : Type -> Type -> Type
Rule token ty = Grammar token True ty

public export
EmptyRule : Type -> Type -> Type
EmptyRule token ty = Grammar token False ty

export
location : {token : _} -> EmptyRule token (Int, Int)
location
    = do tok <- removeIrrelevance <$> bounds peek
         pure $ start tok

export
endLocation : {token : _} -> EmptyRule token (Int, Int)
endLocation
    = do tok <- removeIrrelevance <$> bounds peek
         pure $ end tok

export
position : {token : _} -> EmptyRule token ((Int, Int), (Int, Int))
position
    = do tok <- removeIrrelevance <$> bounds peek
         pure (start tok, end tok)


export
column : {token : _ } -> EmptyRule token Int
column
    = do (line, col) <- location
         pure col
