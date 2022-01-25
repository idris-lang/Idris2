module Libraries.Text.Parser

import Data.Bool
import Data.Nat
import public Data.List1

import public Libraries.Text.Parser.Core
import public Libraries.Text.Quantity
import public Libraries.Text.Token

%default total

||| Parse a terminal based on a kind of token.
export
match : (Eq k, TokenKind k) =>
        (kind : k) ->
        Grammar state (Token k) True (TokType kind)
match k = terminal "Unrecognised input" $
    \t => if t.kind == k
             then Just $ tokValue k t.text
             else Nothing

||| Optionally parse a thing, with a default value if the grammar doesn't
||| match. May match the empty input.
export
option : {c : Bool} ->
         (def : a) -> (p : Grammar state tok c a) ->
         Grammar state tok False a
option {c = False} def p = p <|> pure def
option {c = True} def p = p <|> pure def

||| Optionally parse a thing.
||| To provide a default value, use `option` instead.
export
optional : {c : Bool} ->
           (p : Grammar state tok c a) ->
           Grammar state tok False (Maybe a)
optional p = option Nothing (map Just p)

||| Try to parse one thing or the other, producing a value that indicates
||| which option succeeded. If both would succeed, the left option
||| takes priority.
export
choose : {c1, c2 : Bool} ->
         (l : Grammar state tok c1 a) ->
         (r : Grammar state tok c2 b) ->
         Grammar state tok (c1 && c2) (Either a b)
choose l r = map Left l <|> map Right r

||| Produce a grammar by applying a function to each element of a container,
||| then try each resulting grammar until the first one succeeds. Fails if the
||| container is empty.
export
choiceMap : {c : Bool} ->
            (a -> Grammar state tok c b) ->
            Foldable t => t a ->
            Grammar state tok c b
choiceMap {c} f xs = foldr (\x, acc => rewrite sym (andSameNeutral c) in
                                               f x <|> acc)
                           (fail "No more options") xs

%hide Prelude.(>>=)

||| Try each grammar in a container until the first one succeeds.
||| Fails if the container is empty.
export
choice : Foldable t =>
         {c : Bool} ->
         t (Grammar state tok c a) ->
         Grammar state tok c a
choice = choiceMap id

mutual
  ||| Parse one or more things
  export
  some : Grammar state tok True a ->
         Grammar state tok True (List1 a)
  some p = pure (!p ::: !(many p))

  ||| Parse zero or more things (may match the empty input)
  export
  many : Grammar state tok True a ->
         Grammar state tok False (List a)
  many p = option [] (forget <$> some p)

mutual
  private
  count1 : (q : Quantity) ->
           (p : Grammar state tok True a) ->
           Grammar state tok True (List a)
  count1 q p = do x <- p
                  seq (count q p)
                      (\xs => pure (x :: xs))

  ||| Parse `p`, repeated as specified by `q`, returning the list of values.
  export
  count : (q : Quantity) ->
          (p : Grammar state tok True a) ->
          Grammar state tok (isSucc (min q)) (List a)
  count (Qty Z Nothing) p = many p
  count (Qty Z (Just Z)) _ = pure []
  count (Qty Z (Just (S max))) p = option [] $ count1 (atMost max) p
  count (Qty (S min) Nothing) p = count1 (atLeast min) p
  count (Qty (S min) (Just Z)) _ = fail "Quantity out of order"
  count (Qty (S min) (Just (S max))) p = count1 (between (S min) max) p

mutual
  ||| Parse one or more instances of `p` until `end` succeeds, returning the
  ||| list of values from `p`. Guaranteed to consume input.
  export
  someTill : {c : Bool} ->
             (end : Grammar state tok c e) ->
             (p : Grammar state tok True a) ->
             Grammar state tok True (List1 a)
  someTill {c} end p = do x <- p
                          seq (manyTill end p)
                              (\xs => pure (x ::: xs))

  ||| Parse zero or more instances of `p` until `end` succeeds, returning the
  ||| list of values from `p`. Guaranteed to consume input if `end` consumes.
  export
  manyTill : {c : Bool} ->
             (end : Grammar state tok c e) ->
             (p : Grammar state tok True a) ->
             Grammar state tok c (List a)
  manyTill {c} end p = rewrite sym (andTrueNeutral c) in
                               map (const []) end <|> (forget <$> someTill end p)

mutual
  ||| Parse one or more instance of `skip` until `p` is encountered,
  ||| returning its value.
  export
  afterSome : {c : Bool} ->
              (skip : Grammar state tok True s) ->
              (p : Grammar state tok c a) ->
              Grammar state tok True a
  afterSome skip p = do ignore $ skip
                        afterMany skip p

  ||| Parse zero or more instance of `skip` until `p` is encountered,
  ||| returning its value.
  export
  afterMany : {c : Bool} ->
              (skip : Grammar state tok True s) ->
              (p : Grammar state tok c a) ->
              Grammar state tok c a
  afterMany {c} skip p = rewrite sym (andTrueNeutral c) in
                                 p <|> afterSome skip p

||| Parse one or more things, each separated by another thing.
export
sepBy1 : {c : Bool} ->
         (sep : Grammar state tok True s) ->
         (p : Grammar state tok c a) ->
         Grammar state tok c (List1 a)
sepBy1 {c} sep p = rewrite sym (orFalseNeutral c) in
                           [| p ::: many (sep *> p) |]

||| Parse zero or more things, each separated by another thing. May
||| match the empty input.
export
sepBy : {c : Bool} ->
        (sep : Grammar state tok True s) ->
        (p : Grammar state tok c a) ->
        Grammar state tok False (List a)
sepBy sep p = option [] $ forget <$> sepBy1 sep p

||| Parse one or more instances of `p` separated by and optionally terminated by
||| `sep`.
export
sepEndBy1 : {c : Bool} ->
            (sep : Grammar state tok True s) ->
            (p : Grammar state tok c a) ->
            Grammar state tok c (List1 a)
sepEndBy1 {c} sep p = rewrite sym (orFalseNeutral c) in
                              sepBy1 sep p <* optional sep

||| Parse zero or more instances of `p`, separated by and optionally terminated
||| by `sep`. Will not match a separator by itself.
export
sepEndBy : {c : Bool} ->
           (sep : Grammar state tok True s) ->
           (p : Grammar state tok c a) ->
           Grammar state tok False (List a)
sepEndBy sep p = option [] $ forget <$> sepEndBy1 sep p

||| Parse one or more instances of `p`, separated and terminated by `sep`.
export
endBy1 : {c : Bool} ->
         (sep : Grammar state tok True s) ->
         (p : Grammar state tok c a) ->
         Grammar state tok True (List1 a)
endBy1 {c} sep p = some $ rewrite sym (orTrueTrue c) in
                                  p <* sep

export
endBy : {c : Bool} ->
        (sep : Grammar state tok True s) ->
        (p : Grammar state tok c a) ->
        Grammar state tok False (List a)
endBy sep p = option [] $ forget <$> endBy1 sep p

||| Parse an instance of `p` that is between `left` and `right`.
export
between : {c : Bool} ->
          (left : Grammar state tok True l) ->
          (right : Grammar state tok True r) ->
          (p : Grammar state tok c a) ->
          Grammar state tok True a
between left right contents = left *> contents <* right

export
location : Grammar state token False (Int, Int)
location = startBounds <$> position

export
endLocation : Grammar state token False (Int, Int)
endLocation = endBounds <$> position

export
column : Grammar state token False Int
column = snd <$> location

public export
when : Bool -> Lazy (Grammar state token False ()) -> Grammar state token False ()
when True y = y
when False y = pure ()

public export
%inline
unless : Bool -> Lazy (Grammar state token False ()) -> Grammar state token False ()
unless = when . not
