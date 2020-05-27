module Text.Parser.Core

import Data.List
import public Control.Delayed

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
     Terminal : String -> (tok -> Maybe a) -> Grammar tok True a
     NextIs : String -> (tok -> Bool) -> Grammar tok False tok
     EOF : Grammar tok False ()

     Fail : Bool -> String -> Grammar tok c ty
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

||| Give two alternative grammars. If both consume, the combination is
||| guaranteed to consume.
export %inline
(<|>) : {c1,c2 : Bool} -> 
        Grammar tok c1 ty ->
        Lazy (Grammar tok c2 ty) ->
        Grammar tok (c1 && c2) ty
(<|>) = Alt

||| Allows the result of a grammar to be mapped to a different value.
export
{c : _} ->
Functor (Grammar tok c) where
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
export %inline
pure : (val : ty) -> Grammar tok False ty
pure = Empty

||| Check whether the next token satisfies a predicate
export %inline
nextIs : String -> (tok -> Bool) -> Grammar tok False tok
nextIs = NextIs

||| Look at the next token in the input
export %inline
peek : Grammar tok False tok
peek = nextIs "Unrecognised token" (const True)

||| Succeeds if running the predicate on the next token returns Just x,
||| returning x. Otherwise fails.
export %inline
terminal : String -> (tok -> Maybe a) -> Grammar tok True a
terminal = Terminal

||| Always fail with a message
export %inline
fail : String -> Grammar tok c ty
fail = Fail False

export %inline
fatalError : String -> Grammar tok c ty
fatalError = Fail True

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

data ParseResult : Type -> Type -> Type where
     Failure : (committed : Bool) -> (fatal : Bool) ->
               (err : String) -> (rest : List tok) -> ParseResult tok ty
     Res : (committed : Bool) ->
           (val : ty) -> (more : List tok) -> ParseResult tok ty

mutual
  doParse : (commit : Bool) -> 
            (act : Grammar tok c ty) ->
            (xs : List tok) -> 
            ParseResult tok ty
  doParse com (Empty val) xs = Res com val xs
  doParse com (Fail fatal str) [] = Failure com fatal str []
  doParse com (Fail fatal str) (x :: xs) = Failure com fatal str (x :: xs)
  doParse com Commit xs = Res True () xs
  doParse com (MustWork g) xs =
      let p' = assert_total (doParse com g xs) in
        case p' of
             Failure com' _ msg ts => Failure com' True msg ts
             res => res
  doParse com (Terminal err f) [] = Failure com False "End of input" []
  doParse com (Terminal err f) (x :: xs)
        = case f x of
               Nothing => Failure com False err (x :: xs)
               Just a => Res com a xs
  doParse com EOF [] = Res com () []
  doParse com EOF (x :: xs)
        = Failure com False "Expected end of input" (x :: xs)
  doParse com (NextIs err f) [] = Failure com False "End of input" []
  doParse com (NextIs err f) (x :: xs)
        = if f x
             then Res com x (x :: xs)
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
             Res com val xs =>
                   case assert_total (doParse com (next val) xs) of
                        Failure com' fatal msg ts => Failure com' fatal msg ts
                        Res com' val xs => Res com' val xs
  doParse com (SeqEat act next) xs
      = case assert_total (doParse com act xs) of
             Failure com fatal msg ts => Failure com fatal msg ts
             Res com val xs =>
                   case assert_total (doParse com (next val) xs) of
                        Failure com' fatal msg ts => Failure com' fatal msg ts
                        Res com' val xs => Res com' val xs

public export
data ParsingError tok = Error String (List tok)

||| Parse a list of tokens according to the given grammar. If successful,
||| returns a pair of the parse result and the unparsed tokens (the remaining
||| input).
export
parse : {c : Bool} -> (act : Grammar tok c ty) -> (xs : List tok) ->
        Either (ParsingError tok) (ty, List tok)
parse act xs
    = case doParse False act xs of
           Failure _ _ msg ts => Left (Error msg ts)
           Res _ val rest => pure (val, rest)
