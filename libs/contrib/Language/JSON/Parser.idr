module Language.JSON.Parser

import Language.JSON.Data
import Text.Parser
import Text.Token
import Data.List

import public Language.JSON.Tokens

%default total

private
punct : Punctuation -> Grammar JSONToken True ()
punct p = match $ JTPunct p

private
rawString : Grammar JSONToken True String
rawString = do mstr <- match JTString
               the (Grammar _ False _) $
                   case mstr of
                        Just str => pure str
                        Nothing => fail "invalid string"

mutual
  private
  json : Grammar JSONToken True JSON
  json = object
     <|> array
     <|> string
     <|> boolean
     <|> number
     <|> null

  private
  object : Grammar JSONToken True JSON
  object = do punct $ Curly Open
              commit
              props <- properties
              punct $ Curly Close
              pure $ JObject props
    where
      properties : Grammar JSONToken False (List (String, JSON))
      properties = sepBy (punct Comma) $
                         do key <- rawString
                            punct Colon
                            value <- json
                            pure (key, value)

  private
  array : Grammar JSONToken True JSON
  array = do punct (Square Open)
             commit
             vals <- values
             punct (Square Close)
             pure (JArray vals)
    where
      values : Grammar JSONToken False (List JSON)
      values = sepBy (punct Comma) json

  private
  string : Grammar JSONToken True JSON
  string = map JString rawString

  private
  boolean : Grammar JSONToken True JSON
  boolean = map JBoolean $ match JTBoolean

  private
  number : Grammar JSONToken True JSON
  number = map JNumber $ match JTNumber

  private
  null : Grammar JSONToken True JSON
  null = map (const JNull) $ match JTNull

export
parseJSON : List JSONToken -> Maybe JSON
parseJSON toks = case parse json $ filter (not . ignored) toks of
                      Right (j, []) => Just j
                      _ => Nothing
