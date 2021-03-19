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
location = startBounds <$> position

export
endLocation : {token : _} -> EmptyRule token (Int, Int)
endLocation = endBounds <$> position

export
column : {token : _ } -> EmptyRule token Int
column = snd <$> location
