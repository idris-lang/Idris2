module Text.Parser

import Data.Bool.Extra
import Data.List
import Data.Nat

import public Control.Delayed
import public Text.Bounded
import public Text.Quantity
import public Text.Token

%default total

-- TODO: Add some primitives for helping with error messages.
-- e.g. perhaps set a string to state what we're currently trying to
-- parse, or to say what the next expected token is in words

||| Description of a language's grammar. The `tok` parameter is the type
||| of tokens, and the `consumes` flag is True if the language is guaranteed
||| to be non-empty - that is, successfully parsing the language is guaranteed
||| to consume some input.
export
data Grammar : (tok : Type) -> (consumes : Bool) -> Type -> Type where
     Empty : (val : ty) -> Grammar tok False ty
     Terminal : String -> (WithBounds tok -> Maybe a) -> Grammar tok True a
     NextIs : String -> (WithBounds tok -> Bool) -> Grammar tok False tok
     EOF : Grammar tok False ()

     Fail : Bool -> String -> Grammar tok c ty
     Try : Grammar tok c ty -> Grammar tok c ty

     Commit : Grammar tok False ()
     MustWork : Grammar tok c a -> Grammar tok c a

     SeqEat : {c2 : Bool} ->
              Grammar tok True a -> Inf (a -> Grammar tok c2 b) ->
              Grammar tok True b
     SeqEmpty : {c1, c2 : Bool} ->
                Grammar tok c1 a -> (a -> Grammar tok c2 b) ->
                Grammar tok (c1 || c2) b
     Alt : {c1, c2 : Bool} ->
           Grammar tok c1 ty -> Lazy (Grammar tok c2 ty) ->
           Grammar tok (c1 && c2) ty
     Bounds : Grammar tok c ty -> Grammar tok c (WithBounds ty)

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume some input. If the first one consumes input, the
||| second is allowed to be recursive (because it means some input has been
||| consumed and therefore the input is smaller)
export %inline
(>>=) : {c1, c2 : Bool} ->
        Grammar tok c1 a ->
        inf c1 (a -> Grammar tok c2 b) ->
        Grammar tok (c1 || c2) b
(>>=) {c1 = False} = SeqEmpty
(>>=) {c1 = True}  = SeqEat

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume input. This is an explicitly non-infinite version
||| of `>>=`.
export %inline
seq : {c1,c2 : Bool} ->
      Grammar tok c1 a ->
      (a -> Grammar tok c2 b) ->
      Grammar tok (c1 || c2) b
seq = SeqEmpty

||| Sequence a grammar followed by the grammar it returns.
export %inline
join : {c1,c2 : Bool} ->
       Grammar tok c1 (Grammar tok c2 a) ->
       Grammar tok (c1 || c2) a
join {c1 = False} p = SeqEmpty p id
join {c1 = True} p = SeqEat p id

||| Allows the result of a grammar to be mapped to a different value.
export
{c : _} ->
Functor (Grammar tok c) where
  map f (Empty val)  = Empty (f val)
  map f (Fail fatal msg) = Fail fatal msg
  map f (Try g) = Try (map f g)
  map f (MustWork g) = MustWork (map f g)
  map f (Terminal msg g) = Terminal msg (map f . g)
  map f (Alt x y)    = Alt (map f x) (map f y)
  map f (SeqEat act next)
      = SeqEat act (\val => map f (next val))
  map f (SeqEmpty act next)
      = SeqEmpty act (\val => map f (next val))
  map {c} f (Bounds act) = rewrite sym $ orFalseNeutral c in SeqEmpty (Bounds act) (Empty . f) -- Bounds (map f act)
  -- The remaining constructors (NextIs, EOF, Commit) have a fixed type,
  -- so a sequence must be used.
  map {c = False} f p = SeqEmpty p (Empty . f)

||| Give two alternative grammars. If both consume, the combination is
||| guaranteed to consume.
export %inline
(<|>) : {c1,c2 : Bool} ->
        Grammar tok c1 ty ->
        Lazy (Grammar tok c2 ty) ->
        Grammar tok (c1 && c2) ty
(<|>) = Alt

infixr 2 <||>
||| Take the tagged disjunction of two grammars. If both consume, the
||| combination is guaranteed to consume.
export
(<||>) : {c1,c2 : Bool} ->
        Grammar tok c1 a ->
        Lazy (Grammar tok c2 b) ->
        Grammar tok (c1 && c2) (Either a b)
(<||>) p q = (Left <$> p) <|> (Right <$> q)

||| Sequence a grammar with value type `a -> b` and a grammar
||| with value type `a`. If both succeed, apply the function
||| from the first grammar to the value from the second grammar.
||| Guaranteed to consume if either grammar consumes.
export %inline
(<*>) : {c1, c2 : Bool} ->
        Grammar tok c1 (a -> b) ->
        Grammar tok c2 a ->
        Grammar tok (c1 || c2) b
(<*>) x y = SeqEmpty x (\f => map f y)

||| Sequence two grammars. If both succeed, use the value of the first one.
||| Guaranteed to consume if either grammar consumes.
export %inline
(<*) : {c1,c2 : Bool} ->
       Grammar tok c1 a ->
       Grammar tok c2 b ->
       Grammar tok (c1 || c2) a
(<*) x y = map const x <*> y

||| Sequence two grammars. If both succeed, use the value of the second one.
||| Guaranteed to consume if either grammar consumes.
export %inline
(*>) : {c1,c2 : Bool} ->
       Grammar tok c1 a ->
       Grammar tok c2 b ->
       Grammar tok (c1 || c2) b
(*>) x y = map (const id) x <*> y

||| Produce a grammar that can parse a different type of token by providing a
||| function converting the new token type into the original one.
export
mapToken : (a -> b) -> Grammar b c ty -> Grammar a c ty
mapToken f (Empty val) = Empty val
mapToken f (Terminal msg g) = Terminal msg (g . map f)
mapToken f (NextIs msg g) = SeqEmpty (NextIs msg (g . map f)) (Empty . f)
mapToken f EOF = EOF
mapToken f (Fail fatal msg) = Fail fatal msg
mapToken f (Try g) = Try (mapToken f g)
mapToken f (MustWork g) = MustWork (mapToken f g)
mapToken f Commit = Commit
mapToken f (SeqEat act next) = SeqEat (mapToken f act) (\x => mapToken f (next x))
mapToken f (SeqEmpty act next) = SeqEmpty (mapToken f act) (\x => mapToken f (next x))
mapToken f (Alt x y) = Alt (mapToken f x) (mapToken f y)
mapToken f (Bounds act) = Bounds (mapToken f act)

||| Always succeed with the given value.
export %inline
pure : (val : ty) -> Grammar tok False ty
pure = Empty

||| Check whether the next token satisfies a predicate
export %inline
nextIs : String -> (WithBounds tok -> Bool) -> Grammar tok False tok
nextIs = NextIs

||| Look at the next token in the input
export %inline
peek : Grammar tok False tok
peek = nextIs "Unrecognised token" (const True)

||| Succeeds if running the predicate on the next token returns Just x,
||| returning x. Otherwise fails.
export %inline
terminal : String -> (WithBounds tok -> Maybe a) -> Grammar tok True a
terminal = Terminal

||| Always fail with a message
export %inline
fail : String -> Grammar tok c ty
fail = Fail False

export %inline
fatalError : String -> Grammar tok c ty
fatalError = Fail True

||| Catch a fatal error
export %inline
try : Grammar tok c ty -> Grammar tok c ty
try = Try

||| Succeed if the input is empty
export %inline
eof : Grammar tok False ()
eof = EOF

||| Commit to an alternative; if the current branch of an alternative
||| fails to parse, no more branches will be tried
export %inline
commit : Grammar tok False ()
commit = Commit

||| If the parser fails, treat it as a fatal error
export %inline
mustWork : {c : Bool} -> Grammar tok c ty -> Grammar tok c ty
mustWork = MustWork

export %inline
bounds : Grammar tok c ty -> Grammar tok c (WithBounds ty)
bounds = Bounds

data ParseResult : Type -> Type -> Type where
     Failure : (committed : Bool) -> (fatal : Bool) ->
               (err : String) -> (rest : List (WithBounds tok)) -> ParseResult tok ty
     Res : (committed : Bool) ->
           (val : WithBounds ty) -> (more : List (WithBounds tok)) -> ParseResult tok ty

mutual
  doParse : (commit : Bool) ->
            (act : Grammar tok c ty) ->
            (xs : List (WithBounds tok)) ->
            ParseResult tok ty
  doParse com (Empty val) xs = Res com (irrelevantBounds val) xs
  doParse com (Fail fatal str) xs = Failure com fatal str xs
  doParse com (Try g) xs = case doParse com g xs of
    -- recover from fatal match but still propagate the 'commit'
    Failure com _ msg ts => Failure com False msg ts
    res => res
  doParse com Commit xs = Res True (irrelevantBounds ()) xs
  doParse com (MustWork g) xs =
    case assert_total (doParse com g xs) of
         Failure com' _ msg ts => Failure com' True msg ts
         res => res
  doParse com (Terminal err f) [] = Failure com False "End of input" []
  doParse com (Terminal err f) (x :: xs) =
    case f x of
         Nothing => Failure com False err (x :: xs)
         Just a => Res com (const a <$> x) xs
  doParse com EOF [] = Res com (irrelevantBounds ()) []
  doParse com EOF (x :: xs) = Failure com False "Expected end of input" (x :: xs)
  doParse com (NextIs err f) [] = Failure com False "End of input" []
  doParse com (NextIs err f) (x :: xs)
        = if f x
             then Res com (removeIrrelevance x) (x :: xs)
             else Failure com False err (x :: xs)
  doParse com (Alt {c1} {c2} x y) xs
      = case doParse False x xs of
             Failure com' fatal msg ts
                => if com' || fatal
                          -- If the alternative had committed, don't try the
                          -- other branch (and reset commit flag)
                     then Failure com fatal msg ts
                     else assert_total (doParse False y xs)
-- Successfully parsed the first option, so use the outer commit flag
             Res _ val xs => Res com val xs
  doParse com (SeqEmpty act next) xs
      = case assert_total (doParse com act xs) of
             Failure com fatal msg ts => Failure com fatal msg ts
             Res com v xs =>
               case assert_total (doParse com (next v.val) xs) of
                    Failure com' fatal msg ts => Failure com' fatal msg ts
                    Res com' v' xs => Res com' (mergeBounds v v') xs
  doParse com (SeqEat act next) xs
      = case assert_total (doParse com act xs) of
             Failure com fatal msg ts => Failure com fatal msg ts
             Res com v xs =>
                   case assert_total (doParse com (next v.val) xs) of
                        Failure com' fatal msg ts => Failure com' fatal msg ts
                        Res com' v' xs => Res com' (mergeBounds v v') xs
  doParse com (Bounds act) xs
      = case assert_total (doParse com act xs) of
             Failure com fatal msg ts => Failure com fatal msg ts
             Res com v xs => Res com (const v <$> v) xs

public export
data ParsingError tok = Error String (List (WithBounds tok))

||| Parse a list of tokens according to the given grammar. If successful,
||| returns a pair of the parse result and the unparsed tokens (the remaining
||| input).
export
parse : {c : Bool} -> (act : Grammar tok c ty) -> (xs : List (WithBounds tok)) ->
        Either (ParsingError tok) (ty, List (WithBounds tok))
parse act xs
    = case doParse False act xs of
           Failure _ _ msg ts => Left (Error msg ts)
           Res _ v rest => Right (v.val, rest)


||| Parse a terminal based on a kind of token.
export
match : (Eq k, TokenKind k) =>
        (kind : k) ->
        Grammar (Token k) True (TokType kind)
match k = terminal "Unrecognised input" $
    \t => if t.val.kind == k
             then Just $ tokValue k t.val.text
             else Nothing

||| Optionally parse a thing, with a default value if the grammar doesn't
||| match. May match the empty input.
export
option : {c : Bool} ->
         (def : a) -> (p : Grammar tok c a) ->
         Grammar tok False a
option {c = False} def p = p <|> pure def
option {c = True} def p = p <|> pure def

||| Optionally parse a thing.
||| To provide a default value, use `option` instead.
export
optional : {c : Bool} ->
           (p : Grammar tok c a) ->
           Grammar tok False (Maybe a)
optional p = option Nothing (map Just p)

||| Try to parse one thing or the other, producing a value that indicates
||| which option succeeded. If both would succeed, the left option
||| takes priority.
export
choose : {c1, c2 : Bool} -> 
         (l : Grammar tok c1 a) ->
         (r : Grammar tok c2 b) ->
         Grammar tok (c1 && c2) (Either a b)
choose l r = map Left l <|> map Right r

||| Produce a grammar by applying a function to each element of a container,
||| then try each resulting grammar until the first one succeeds. Fails if the
||| container is empty.
export
choiceMap : {c : Bool} ->
            (a -> Grammar tok c b) ->
            Foldable t => t a ->
            Grammar tok c b
choiceMap {c} f xs = foldr (\x, acc => rewrite sym (andSameNeutral c) in
                                               f x <|> acc)
                           (fail "No more options") xs

%hide Prelude.(>>=)

||| Try each grammar in a container until the first one succeeds.
||| Fails if the container is empty.
export
choice : Foldable t => 
         {c : Bool} ->
         t (Grammar tok c a) ->
         Grammar tok c a
choice = choiceMap id

mutual
  ||| Parse one or more things
  export
  some : Grammar tok True a ->
         Grammar tok True (List a)
  some p = pure (!p :: !(many p))

  ||| Parse zero or more things (may match the empty input)
  export
  many : Grammar tok True a ->
         Grammar tok False (List a)
  many p = option [] (some p)

||| Parse one or more instances of `p`, returning the parsed items and proof
||| that the resulting list is non-empty.
export
some' : (p : Grammar tok True a) ->
        Grammar tok True (xs : List a ** NonEmpty xs)
some' p = pure (!p :: !(many p) ** IsNonEmpty)

mutual
  private
  count1 : (q : Quantity) ->
           (p : Grammar tok True a) ->
           Grammar tok True (List a)
  count1 q p = do x <- p
                  seq (count q p)
                      (\xs => pure (x :: xs))

  ||| Parse `p`, repeated as specified by `q`, returning the list of values.
  export
  count : (q : Quantity) ->
          (p : Grammar tok True a) ->
          Grammar tok (isSucc (min q)) (List a)
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
             (end : Grammar tok c e) ->
             (p : Grammar tok True a) ->
             Grammar tok True (List a)
  someTill {c} end p = do x <- p
                          seq (manyTill end p)
                              (\xs => pure (x :: xs))

  ||| Parse zero or more instances of `p` until `end` succeeds, returning the
  ||| list of values from `p`. Guaranteed to consume input if `end` consumes.
  export
  manyTill : {c : Bool} ->
             (end : Grammar tok c e) ->
             (p : Grammar tok True a) ->
             Grammar tok c (List a)
  manyTill {c} end p = rewrite sym (andTrueNeutral c) in
                               map (const []) end <|> someTill end p

||| Parse one or more instances of `p` until `end` succeeds, returning the
||| list of values from `p`, along with a proof that the resulting list is
||| non-empty.
export
someTill' : {c : Bool} ->
            (end : Grammar tok c e) ->
            (p : Grammar tok True a) ->
            Grammar tok True (xs : List a ** NonEmpty xs)
someTill' end p
  = do x <- p
       seq (manyTill end p)
           (\xs => pure (x :: xs ** IsNonEmpty))

mutual
  ||| Parse one or more instance of `skip` until `p` is encountered,
  ||| returning its value.
  export
  afterSome : {c : Bool} ->
              (skip : Grammar tok True s) ->
              (p : Grammar tok c a) ->
              Grammar tok True a
  afterSome skip p = do skip
                        afterMany skip p

  ||| Parse zero or more instance of `skip` until `p` is encountered,
  ||| returning its value.
  export
  afterMany : {c : Bool} ->
              (skip : Grammar tok True s) ->
              (p : Grammar tok c a) ->
              Grammar tok c a
  afterMany {c} skip p = rewrite sym (andTrueNeutral c) in
                                 p <|> afterSome skip p

||| Parse one or more things, each separated by another thing.
export
sepBy1 : {c : Bool} ->
         (sep : Grammar tok True s) ->
         (p : Grammar tok c a) ->
         Grammar tok c (List a)
sepBy1 {c} sep p = rewrite sym (orFalseNeutral c) in
                           [| p :: many (sep *> p) |]

||| Parse zero or more things, each separated by another thing. May
||| match the empty input.
export
sepBy : {c : Bool} ->
        (sep : Grammar tok True s) ->
        (p : Grammar tok c a) ->
        Grammar tok False (List a)
sepBy sep p = option [] $ sepBy1 sep p

||| Parse one or more instances of `p` separated by `sep`, returning the
||| parsed items and proof that the resulting list is non-empty.
export
sepBy1' : {c : Bool} ->
         (sep : Grammar tok True s) ->
         (p : Grammar tok c a) ->
         Grammar tok c (xs : List a ** NonEmpty xs)
sepBy1' {c} sep p
  = rewrite sym (orFalseNeutral c) in
            seq p (\x => do xs <- many (sep *> p)
                            pure (x :: xs ** IsNonEmpty))

||| Parse one or more instances of `p` separated by and optionally terminated by
||| `sep`.
export
sepEndBy1 : {c : Bool} ->
            (sep : Grammar tok True s) ->
            (p : Grammar tok c a) ->
            Grammar tok c (List a)
sepEndBy1 {c} sep p = rewrite sym (orFalseNeutral c) in
                              sepBy1 sep p <* optional sep

||| Parse zero or more instances of `p`, separated by and optionally terminated
||| by `sep`. Will not match a separator by itself.
export
sepEndBy : {c : Bool} ->
           (sep : Grammar tok True s) ->
           (p : Grammar tok c a) ->
           Grammar tok False (List a)
sepEndBy sep p = option [] $ sepEndBy1 sep p

||| Parse zero or more instances of `p`, separated by and optionally terminated
||| by `sep`, returning the parsed items and a proof that the resulting list
||| is non-empty.
export
sepEndBy1' : {c : Bool} ->
             (sep : Grammar tok True s) ->
             (p : Grammar tok c a) ->
             Grammar tok c (xs : List a ** NonEmpty xs)
sepEndBy1' {c} sep p = rewrite sym (orFalseNeutral c) in
                               sepBy1' sep p <* optional sep

||| Parse one or more instances of `p`, separated and terminated by `sep`.
export
endBy1 : {c : Bool} ->
         (sep : Grammar tok True s) ->
         (p : Grammar tok c a) ->
         Grammar tok True (List a)
endBy1 {c} sep p = some $ rewrite sym (orTrueTrue c) in
                                  p <* sep

export
endBy : {c : Bool} ->
        (sep : Grammar tok True s) ->
        (p : Grammar tok c a) ->
        Grammar tok False (List a)
endBy sep p = option [] $ endBy1 sep p

||| Parse zero or more instances of `p`, separated and terminated by `sep`,
||| returning the parsed items and a proof that the resulting list is non-empty.
export
endBy1' : {c : Bool} ->
          (sep : Grammar tok True s) ->
          (p : Grammar tok c a) ->
          Grammar tok True (xs : List a ** NonEmpty xs)
endBy1' {c} sep p = some' $ rewrite sym (orTrueTrue c) in
                                    p <* sep

||| Parse an instance of `p` that is between `left` and `right`.
export
between : {c : Bool} ->
          (left : Grammar tok True l) ->
          (right : Grammar tok True r) ->
          (p : Grammar tok c a) ->
          Grammar tok True a
between left right contents = left *> contents <* right
