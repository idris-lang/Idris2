||| The JSON language, as described at https://json.org/
module Language.JSON

import Language.JSON.Lexer
import Language.JSON.Parser

import public Language.JSON.Data

%default total

||| Parse a JSON string.
export
parse : String -> Maybe JSON
parse x = parseJSON !(lexJSON x)
