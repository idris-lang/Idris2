module Language.JSON.Parser

import Language.JSON.Data
import Text.Parser
import Data.List

import public Language.JSON.Tokens

%default total

private
punct : Punctuation -> Grammar state JSONToken True ()
punct p = match $ JTPunct p

private
rawString : Grammar state JSONToken True String
rawString = do mstr <- match JTString
               the (Grammar _ _ False _) $
                   case mstr of
                        Just str => pure str
                        Nothing => fail "invalid string"

mutual
  private
  json : Grammar state JSONToken True JSON
  json = object
     <|> array
     <|> string
     <|> boolean
     <|> number
     <|> null

  private
  object : Grammar state JSONToken True JSON
  object = do punct $ Curly Open
              commit
              props <- properties
              punct $ Curly Close
              pure $ JObject props
    where
      properties : Grammar state JSONToken False (List (String, JSON))
      properties = sepBy (punct Comma) $
                         do key <- rawString
                            punct Colon
                            value <- json
                            pure (key, value)

  private
  array : Grammar state JSONToken True JSON
  array = do punct (Square Open)
             commit
             vals <- values
             punct (Square Close)
             pure (JArray vals)
    where
      values : Grammar state JSONToken False (List JSON)
      values = sepBy (punct Comma) json

  private
  string : Grammar state JSONToken True JSON
  string = map JString rawString

  private
  boolean : Grammar state JSONToken True JSON
  boolean = map JBoolean $ match JTBoolean

  private
  number : Grammar state JSONToken True JSON
  number = map JNumber $ match JTNumber

  private
  null : Grammar state JSONToken True JSON
  null = map (const JNull) $ match JTNull

export
parseJSON : List (WithBounds JSONToken) -> Maybe JSON
parseJSON toks = case parse json $ filter (not . ignored) toks of
                      Right (j, []) => Just j
                      _ => Nothing
