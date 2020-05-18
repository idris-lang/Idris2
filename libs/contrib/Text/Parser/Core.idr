module Text.Parser.Core

import public Control.Delayed
import Data.List

||| Description of a language's grammar. The `tok` parameter is the type
||| of tokens, and the `consumes` flag is True if the language is guaranteed
||| to be non-empty - that is, successfully parsing the language is guaranteed
||| to consume some input.
public export
data Grammar : (tok : Type) -> (consumes : Bool) -> Type -> Type where
     Empty : (val : ty) -> Grammar tok False ty
     Terminal : String -> (tok -> Maybe a) -> Grammar tok True a
     NextIs : String -> (tok -> Bool) -> Grammar tok False tok
     EOF : Grammar tok False ()

     Fail : Bool -> String -> Grammar tok c ty
     Commit : Grammar tok False ()
     MustWork : Grammar tok c a -> Grammar tok c a

     SeqEat : {c2 : _} -> Grammar tok True a -> Inf (a -> Grammar tok c2 b) ->
              Grammar tok True b
     SeqEmpty : {c1, c2 : _} -> Grammar tok c1 a -> (a -> Grammar tok c2 b) ->
                Grammar tok (c1 || c2) b
     Alt : {c1, c2 : _} -> Grammar tok c1 ty -> Grammar tok c2 ty ->
           Grammar tok (c1 && c2) ty

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume some input. If the first one consumes input, the
||| second is allowed to be recursive (because it means some input has been
||| consumed and therefore the input is smaller)
public export %inline
(>>=) : {c1, c2 : Bool} ->
        Grammar tok c1 a ->
        inf c1 (a -> Grammar tok c2 b) ->
        Grammar tok (c1 || c2) b
(>>=) {c1 = False} = SeqEmpty
(>>=) {c1 = True} = SeqEat

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume input. This is an explicitly non-infinite version
||| of `>>=`.
export
seq : {c1, c2 : _} -> Grammar tok c1 a ->
      (a -> Grammar tok c2 b) ->
      Grammar tok (c1 || c2) b
seq = SeqEmpty

||| Sequence a grammar followed by the grammar it returns.
export
join : {c1, c2 : Bool} ->
       Grammar tok c1 (Grammar tok c2 a) ->
       Grammar tok (c1 || c2) a
join {c1 = False} p = SeqEmpty p id
join {c1 = True} p = SeqEat p id

||| Give two alternative grammars. If both consume, the combination is
||| guaranteed to consume.
export
(<|>) : {c1, c2 : _} ->
        Grammar tok c1 ty ->
        Grammar tok c2 ty ->
        Grammar tok (c1 && c2) ty
(<|>) = Alt

||| Allows the result of a grammar to be mapped to a different value.
export
{c : _} -> Functor (Grammar tok c) where
  map f (Empty val)  = Empty (f val)
  map f (Fail fatal msg) = Fail fatal msg
  map f (MustWork g) = MustWork (map f g)
  map f (Terminal msg g) = Terminal msg (\t => map f (g t))
  map f (Alt x y)    = Alt (map f x) (map f y)
  map f (SeqEat act next)
      = SeqEat act (\val => map f (next val))
  map f (SeqEmpty act next)
      = SeqEmpty act (\val => map f (next val))
  -- The remaining constructors (NextIs, EOF, Commit) have a fixed type,
  -- so a sequence must be used.
  map {c = False} f p = SeqEmpty p (Empty . f)

||| Sequence a grammar with value type `a -> b` and a grammar
||| with value type `a`. If both succeed, apply the function
||| from the first grammar to the value from the second grammar.
||| Guaranteed to consume if either grammar consumes.
export
(<*>) : {c1, c2 : _} ->
        Grammar tok c1 (a -> b) ->
        Inf (Grammar tok c2 a) ->
        Grammar tok (c1 || c2) b
(<*>) {c1 = False} x y = SeqEmpty x (\f => map f y)
(<*>) {c1 = True } x y = SeqEmpty x (\f => map f (Force y))

||| Sequence two grammars. If both succeed, use the value of the first one.
||| Guaranteed to consume if either grammar consumes.
export
(<*) : {c1, c2 : _} ->
       Grammar tok c1 a ->
       Inf (Grammar tok c2 b) ->
       Grammar tok (c1 || c2) a
(<*) x y = map const x <*> y

||| Sequence two grammars. If both succeed, use the value of the second one.
||| Guaranteed to consume if either grammar consumes.
export
(*>) : {c1, c2 : _} ->
       Grammar tok c1 a ->
       Inf (Grammar tok c2 b) ->
       Grammar tok (c1 || c2) b
(*>) x y = map (const id) x <*> y

||| Produce a grammar that can parse a different type of token by providing a
||| function converting the new token type into the original one.
export
mapToken : (a -> b) -> Grammar b c ty -> Grammar a c ty
mapToken f (Empty val) = Empty val
mapToken f (Terminal msg g) = Terminal msg (g . f)
mapToken f (NextIs msg g) = SeqEmpty (NextIs msg (g . f)) (Empty . f)
mapToken f EOF = EOF
mapToken f (Fail fatal msg) = Fail fatal msg
mapToken f (MustWork g) = MustWork (mapToken f g)
mapToken f Commit = Commit
mapToken f (SeqEat act next) = SeqEat (mapToken f act) (\x => mapToken f (next x))
mapToken f (SeqEmpty act next) = SeqEmpty (mapToken f act) (\x => mapToken f (next x))
mapToken f (Alt x y) = Alt (mapToken f x) (mapToken f y)

||| Always succeed with the given value.
export
pure : (val : ty) -> Grammar tok False ty
pure = Empty

||| Check whether the next token satisfies a predicate
export
nextIs : String -> (tok -> Bool) -> Grammar tok False tok
nextIs = NextIs

||| Look at the next token in the input
export
peek : Grammar tok False tok
peek = nextIs "Unrecognised token" (const True)

||| Succeeds if running the predicate on the next token returns Just x,
||| returning x. Otherwise fails.
export
terminal : String -> (tok -> Maybe a) -> Grammar tok True a
terminal = Terminal

||| Always fail with a message
export
fail : String -> Grammar tok c ty
fail = Fail False

export
fatalError : String -> Grammar tok c ty
fatalError = Fail True

||| Succeed if the input is empty
export
eof : Grammar tok False ()
eof = EOF

||| Commit to an alternative; if the current branch of an alternative
||| fails to parse, no more branches will be tried
export
commit : Grammar tok False ()
commit = Commit

||| If the parser fails, treat it as a fatal error
export
mustWork : Grammar tok c ty -> Grammar tok c ty
mustWork = MustWork

data ParseResult : List tok -> (consumes : Bool) -> Type -> Type where
     Failure : {xs : List tok} ->
               (committed : Bool) -> (fatal : Bool) ->
               (err : String) -> (rest : List tok) -> ParseResult xs c ty
     EmptyRes : (committed : Bool) ->
                (val : ty) -> (more : List tok) -> ParseResult more False ty
     NonEmptyRes : {xs : List tok} ->
                   (committed : Bool) ->
                   (val : ty) -> (more : List tok) ->
                   ParseResult (x :: xs ++ more) c ty

-- Take the result of an alternative branch, reset the commit flag to
-- the commit flag from the outer alternative, and weaken the 'consumes'
-- flag to take both alternatives into account
weakenRes : {whatever, c : Bool} -> {xs : List tok} ->
            (com' : Bool) ->
						ParseResult xs c ty -> ParseResult xs (whatever && c) ty
weakenRes com' (Failure com fatal msg ts) = Failure com' fatal msg ts
weakenRes {whatever=True} com' (EmptyRes com val xs) = EmptyRes com' val xs
weakenRes {whatever=False} com' (EmptyRes com val xs) = EmptyRes com' val xs
weakenRes com' (NonEmptyRes {xs} com val more) = NonEmptyRes {xs} com' val more

doParse : (commit : Bool) -> 
          (act : Grammar tok c ty) ->
          (xs : List tok) -> 
          ParseResult xs c ty
-- doParse com xs act with (sizeAccessible xs)
doParse com (Empty val) xs = EmptyRes com val xs
doParse com (Fail fatal str) [] = Failure com fatal str []
doParse com (Fail fatal str) (x :: xs) = Failure com fatal str (x :: xs)
doParse com Commit xs = EmptyRes True () xs
doParse com (MustWork g) xs =
  let p' = doParse com g xs in
      case p' of
           Failure com' _ msg ts => Failure com' True msg ts
           res => res
doParse com (Terminal err f) [] = Failure com False "End of input" []
doParse com (Terminal err f) (x :: xs)
      = maybe
           (Failure com False err (x :: xs))
           (\a => NonEmptyRes com {xs=[]} a xs)
           (f x)
doParse com EOF [] = EmptyRes com () []
doParse com EOF (x :: xs)
      = Failure com False "Expected end of input" (x :: xs)
doParse com (NextIs err f) [] = Failure com False "End of input" []
doParse com (NextIs err f) (x :: xs)
      = if f x
           then EmptyRes com x (x :: xs)
           else Failure com False err (x :: xs)
doParse com (Alt {c1} {c2} x y) xs
    = let p' = doParse False x xs in
          case p' of
               Failure com' fatal msg ts
                  => if com' || fatal
                            -- If the alternative had committed, don't try the
                            -- other branch (and reset commit flag)
                       then Failure com fatal msg ts
                       else weakenRes {whatever = c1} com (doParse False y xs)
  -- Successfully parsed the first option, so use the outer commit flag
               EmptyRes _ val xs => EmptyRes com val xs
               NonEmptyRes {xs=xs'} _ val more => NonEmptyRes {xs=xs'} com val more
doParse com (SeqEmpty {c1} {c2} act next) xs
    = let p' = assert_total (doParse {c = c1} com act xs) in
              case p' of
               Failure com fatal msg ts => Failure com fatal msg ts
               EmptyRes com val xs =>
                     case assert_total (doParse com (next val) xs) of
                          Failure com' fatal msg ts => Failure com' fatal msg ts
                          EmptyRes com' val xs => EmptyRes com' val xs
                          NonEmptyRes {xs=xs'} com' val more => 
                                           NonEmptyRes {xs=xs'} com' val more
               NonEmptyRes {x} {xs=ys} com val more =>
                     case (assert_total (doParse com (next val) more)) of
                          Failure com' fatal msg ts => Failure com' fatal msg ts
                          EmptyRes com' val _ => NonEmptyRes {xs=ys} com' val more
                          NonEmptyRes {x=x1} {xs=xs1} com' val more' =>
                               rewrite appendAssociative (x :: ys) (x1 :: xs1) more' in
                                       NonEmptyRes {xs = ys ++ (x1 :: xs1)} com' val more'
doParse com (SeqEat act next) xs with (doParse com act xs)
  doParse com (SeqEat act next) xs | Failure com' fatal msg ts
       = Failure com' fatal msg ts
  doParse com (SeqEat act next) (x :: (ys ++ more)) | (NonEmptyRes {xs=ys} com' val more)
       = let p' = assert_total (doParse com' (next val) more) in
             case p' of
              Failure com' fatal msg ts => Failure com' fatal msg ts
              EmptyRes com' val _ => NonEmptyRes {xs=ys} com' val more
              NonEmptyRes {x=x1} {xs=xs1} com' val more' =>
                   rewrite appendAssociative (x :: ys) (x1 :: xs1) more' in
                           NonEmptyRes {xs = ys ++ (x1 :: xs1)} com' val more'
-- This next line is not strictly necessary, but it stops the coverage
-- checker taking a really long time and eating lots of memory...
-- doParse _ _ _ = Failure True True "Help the coverage checker!" []

public export
data ParseError tok = Error String (List tok)

||| Parse a list of tokens according to the given grammar. If successful,
||| returns a pair of the parse result and the unparsed tokens (the remaining
||| input).
export
parse : {c : _} -> (act : Grammar tok c ty) -> (xs : List tok) ->
        Either (ParseError tok) (ty, List tok)
parse act xs
    = case doParse False act xs of
           Failure _ _ msg ts => Left (Error msg ts)
           EmptyRes _ val rest => pure (val, rest)
           NonEmptyRes _ val rest => pure (val, rest)
