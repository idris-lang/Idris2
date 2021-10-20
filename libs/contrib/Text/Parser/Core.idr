module Text.Parser.Core

import Data.Bool
import Data.List
import Data.List1

import public Control.Delayed
import Control.Monad.State
import public Text.Bounded

%default total

-- TODO: Add some primitives for helping with error messages.
-- e.g. perhaps set a string to state what we're currently trying to
-- parse, or to say what the next expected token is in words

||| Description of a language's grammar. The `tok` parameter is the type
||| of tokens, and the `consumes` flag is True if the language is guaranteed
||| to be non-empty - that is, successfully parsing the language is guaranteed
||| to consume some input.
export
data Grammar : (state : Type) -> (tok : Type) -> (consumes : Bool) -> Type -> Type where
     Empty : (val : ty) -> Grammar state tok False ty
     Terminal : String -> (tok -> Maybe a) -> Grammar state tok True a
     NextIs : String -> (tok -> Bool) -> Grammar state tok False tok
     EOF : Grammar state tok False ()

     Fail : (location : Maybe Bounds) -> (fatal : Bool) -> String -> Grammar state tok c ty
     Try : Grammar state tok c ty -> Grammar state tok c ty

     Commit : Grammar state tok False ()
     MustWork : Grammar state tok c a -> Grammar state tok c a

     SeqEat : {c2 : Bool} ->
              Grammar state tok True a -> Inf (a -> Grammar state tok c2 b) ->
              Grammar state tok True b
     SeqEmpty : {c1, c2 : Bool} ->
                Grammar state tok c1 a -> (a -> Grammar state tok c2 b) ->
                Grammar state tok (c1 || c2) b

     ThenEat : {c2 : Bool} ->
               Grammar state tok True () -> Inf (Grammar state tok c2 a) ->
               Grammar state tok True a
     ThenEmpty : {c1, c2 : Bool} ->
                 Grammar state tok c1 () -> Grammar state tok c2 a ->
                 Grammar state tok (c1 || c2) a

     Alt : {c1, c2 : Bool} ->
           Grammar state tok c1 ty -> Lazy (Grammar state tok c2 ty) ->
           Grammar state tok (c1 && c2) ty
     Bounds : Grammar state tok c ty -> Grammar state tok c (WithBounds ty)
     Position : Grammar state tok False Bounds

     Act : state -> Grammar state tok False ()

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume some input. If the first one consumes input, the
||| second is allowed to be recursive (because it means some input has been
||| consumed and therefore the input is smaller)
export %inline
(>>=) : {c1, c2 : Bool} ->
        Grammar state tok c1 a ->
        inf c1 (a -> Grammar state tok c2 b) ->
        Grammar state tok (c1 || c2) b
(>>=) {c1 = False} = SeqEmpty
(>>=) {c1 = True}  = SeqEat

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume some input. If the first one consumes input, the
||| second is allowed to be recursive (because it means some input has been
||| consumed and therefore the input is smaller)
public export %inline %tcinline
(>>) : {c1, c2 : Bool} ->
        Grammar state tok c1 () ->
        inf c1 (Grammar state tok c2 a) ->
        Grammar state tok (c1 || c2) a
(>>) {c1 = False} = ThenEmpty
(>>) {c1 = True} = ThenEat

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume input. This is an explicitly non-infinite version
||| of `>>=`.
export %inline
seq : {c1,c2 : Bool} ->
      Grammar state tok c1 a ->
      (a -> Grammar state tok c2 b) ->
      Grammar state tok (c1 || c2) b
seq = SeqEmpty

||| Sequence a grammar followed by the grammar it returns.
export %inline
join : {c1,c2 : Bool} ->
       Grammar state tok c1 (Grammar state tok c2 a) ->
       Grammar state tok (c1 || c2) a
join {c1 = False} p = SeqEmpty p id
join {c1 = True} p = SeqEat p id

||| Allows the result of a grammar to be mapped to a different value.
export
{c : _} ->
Functor (Grammar state tok c) where
  map f (Empty val)  = Empty (f val)
  map f (Fail bd fatal msg) = Fail bd fatal msg
  map f (Try g) = Try (map f g)
  map f (MustWork g) = MustWork (map f g)
  map f (Terminal msg g) = Terminal msg (map f . g)
  map f (Alt x y)    = Alt (map f x) (map f y)
  map f (SeqEat act next)
      = SeqEat act (\val => map f (next val))
  map f (SeqEmpty act next)
      = SeqEmpty act (\ val => map f (next val))
  map f (ThenEat act next)
      = ThenEat act (map f next)
  map f (ThenEmpty act next)
      = ThenEmpty act (map f next)
  map {c} f (Bounds act)
    = rewrite sym $ orFalseNeutral c in
      SeqEmpty (Bounds act) (Empty . f) -- Bounds (map f act)
  -- The remaining constructors (NextIs, EOF, Commit) have a fixed type,
  -- so a sequence must be used.
  map {c = False} f p = SeqEmpty p (Empty . f)

||| Give two alternative grammars. If both consume, the combination is
||| guaranteed to consume.
export %inline
(<|>) : {c1,c2 : Bool} ->
        Grammar state tok c1 ty ->
        Lazy (Grammar state tok c2 ty) ->
        Grammar state tok (c1 && c2) ty
(<|>) = Alt

infixr 2 <||>
||| Take the tagged disjunction of two grammars. If both consume, the
||| combination is guaranteed to consume.
export
(<||>) : {c1,c2 : Bool} ->
        Grammar state tok c1 a ->
        Lazy (Grammar state tok c2 b) ->
        Grammar state tok (c1 && c2) (Either a b)
(<||>) p q = (Left <$> p) <|> (Right <$> q)

||| Sequence a grammar with value type `a -> b` and a grammar
||| with value type `a`. If both succeed, apply the function
||| from the first grammar to the value from the second grammar.
||| Guaranteed to consume if either grammar consumes.
export %inline
(<*>) : {c1, c2 : Bool} ->
        Grammar state tok c1 (a -> b) ->
        Grammar state tok c2 a ->
        Grammar state tok (c1 || c2) b
(<*>) x y = SeqEmpty x (\f => map f y)

||| Sequence two grammars. If both succeed, use the value of the first one.
||| Guaranteed to consume if either grammar consumes.
export %inline
(<*) : {c1,c2 : Bool} ->
       Grammar state tok c1 a ->
       Grammar state tok c2 b ->
       Grammar state tok (c1 || c2) a
(<*) x y = map const x <*> y

||| Sequence two grammars. If both succeed, use the value of the second one.
||| Guaranteed to consume if either grammar consumes.
export %inline
(*>) : {c1,c2 : Bool} ->
       Grammar state tok c1 a ->
       Grammar state tok c2 b ->
       Grammar state tok (c1 || c2) b
(*>) x y = map (const id) x <*> y

export %inline
act : state -> Grammar state tok False ()
act = Act

||| Produce a grammar that can parse a different type of token by providing a
||| function converting the new token type into the original one.
export
mapToken : (a -> b) -> Grammar state b c ty -> Grammar state a c ty
mapToken f (Empty val) = Empty val
mapToken f (Terminal msg g) = Terminal msg (g . f)
mapToken f (NextIs msg g) = SeqEmpty (NextIs msg (g . f)) (Empty . f)
mapToken f EOF = EOF
mapToken f (Fail bd fatal msg) = Fail bd fatal msg
mapToken f (Try g) = Try (mapToken f g)
mapToken f (MustWork g) = MustWork (mapToken f g)
mapToken f Commit = Commit
mapToken f (SeqEat act next)
  = SeqEat (mapToken f act) (\x => mapToken f (next x))
mapToken f (SeqEmpty act next)
  = SeqEmpty (mapToken f act) (\x => mapToken f (next x))
mapToken f (ThenEat act next)
  = ThenEat (mapToken f act) (mapToken f next)
mapToken f (ThenEmpty act next)
  = ThenEmpty (mapToken f act) (mapToken f next)
mapToken f (Alt x y) = Alt (mapToken f x) (mapToken f y)
mapToken f (Bounds act) = Bounds (mapToken f act)
mapToken f Position = Position
mapToken f (Act action) = Act action

||| Always succeed with the given value.
export %inline
pure : (val : ty) -> Grammar state tok False ty
pure = Empty

||| Check whether the next token satisfies a predicate
export %inline
nextIs : String -> (tok -> Bool) -> Grammar state tok False tok
nextIs = NextIs

||| Look at the next token in the input
export %inline
peek : Grammar state tok False tok
peek = nextIs "Unrecognised token" (const True)

||| Succeeds if running the predicate on the next token returns Just x,
||| returning x. Otherwise fails.
export %inline
terminal : String -> (tok -> Maybe a) -> Grammar state tok True a
terminal = Terminal

||| Always fail with a message
export %inline
fail : String -> Grammar state tok c ty
fail = Fail Nothing False

||| Always fail with a message and a location
export %inline
failLoc : Bounds -> String -> Grammar state tok c ty
failLoc b = Fail (Just b) False

||| Fail with no possibility for recovery (i.e.
||| no alternative parsing can succeed).
export %inline
fatalError : String -> Grammar state tok c ty
fatalError = Fail Nothing True

||| Fail with no possibility for recovery (i.e.
||| no alternative parsing can succeed).
export %inline
fatalLoc : Bounds -> String -> Grammar state tok c ty
fatalLoc b = Fail (Just b) True

||| Catch a fatal error
export %inline
try : Grammar state tok c ty -> Grammar state tok c ty
try = Try

||| Succeed if the input is empty
export %inline
eof : Grammar state tok False ()
eof = EOF

||| Commit to an alternative; if the current branch of an alternative
||| fails to parse, no more branches will be tried
export %inline
commit : Grammar state tok False ()
commit = Commit

||| If the parser fails, treat it as a fatal error
export %inline
mustWork : {c : Bool} -> Grammar state tok c ty -> Grammar state tok c ty
mustWork = MustWork

export %inline
bounds : Grammar state tok c ty -> Grammar state tok c (WithBounds ty)
bounds = Bounds

export %inline
position : Grammar state tok False Bounds
position = Position

public export
data ParsingError tok = Error String (Maybe Bounds)

data ParseResult : Type -> Type -> Type -> Type where
     Failure : (committed : Bool) -> (fatal : Bool) ->
               List1 (ParsingError tok) -> ParseResult state tok ty
     Res : state -> (committed : Bool) ->
           (val : WithBounds ty) -> ParseResult state tok ty

mergeWith : WithBounds ty -> ParseResult state tok sy -> ParseResult state tok sy
mergeWith x (Res s committed val) = Res s committed (mergeBounds x val)
mergeWith x v = v

public export
interface (Monad m) => MonadToken m tok | m where
  nextToken : m (Maybe (WithBounds tok))
  push : m a -> m (a, m ())

doParse : (Semigroup state, MonadToken m tok) => state -> (commit : Bool) ->
          (act : Grammar state tok c ty) ->
          m (ParseResult state tok ty)
doParse s com (Empty val) = pure $ Res s com (irrelevantBounds val)
doParse s com (Fail location fatal str) = do
    mx <- nextToken
    pure $ Failure com fatal (Error str (location <|> (bounds <$> mx)) ::: Nil)
doParse s com (Try g) = doParse s com g <&> \r => case r of
    -- recover from fatal match but still propagate the 'commit'
    Failure com _ errs => Failure com False errs
    res => res
doParse s com Commit = pure $ Res s True (irrelevantBounds ())
doParse s com (MustWork g) = assert_total (doParse s com g) <&> \r => case r of
  Failure com' _ errs => Failure com' True errs
  res => res
doParse s com (Terminal err f) = nextToken <&> \mx => case mx of
  Nothing => Failure com False (Error "End of input" Nothing ::: Nil)
  Just x => case f x.val of
    Nothing => Failure com False (Error err (Just x.bounds) ::: Nil)
    Just a => Res s com (a <$ x)
doParse s com EOF = nextToken <&> \mx => case mx of
  Nothing => Res s com (irrelevantBounds ())
  Just x => Failure com False $
    Error "Expected end of input" (Just x.bounds) ::: Nil
doParse s com (NextIs err f) = do
  (mx, pop) <- push nextToken
  pop $> case mx of
    Nothing => Failure com False (Error "End of input" Nothing ::: Nil)
    Just x => if f x.val
      then Res s com (removeIrrelevance x)
      else Failure com False (Error err (Just x.bounds) ::: Nil)
doParse s com (Alt {c1} {c2} p1 p2) = do
  (r, pop) <- push $ doParse s False p1
  case r of
    -- Successfully parsed the first option, so use the outer commit flag
    Res s _ val => pure $ Res s com val
    Failure com' fatal errs =>
      if com' || fatal
        -- If the alternative had committed, don't try the
        -- other branch (and reset commit flag)
        then pure $ Failure com fatal errs
        else do
          pop
          r <- assert_total (doParse s False p2)
          pure $ case r of
            Failure com'' fatal' errs' =>
              if com'' || fatal'
                 -- Only add the errors together if the second branch is also non-committed and non-fatal.
                 then Failure com'' fatal' errs'
                 else Failure False False (errs ++ errs')
            Res s _ val => Res s com val
doParse s com (SeqEmpty act next) = do
  r <- assert_total $ doParse s com act
  case r of
    Failure com fatal errs => pure $ Failure com fatal errs
    Res s com v => mergeWith v <$> assert_total (doParse s com (next v.val))
doParse s com (SeqEat act next) = do
  r <- assert_total $ doParse s com act
  case r of
    Failure com fatal errs => pure $ Failure com fatal errs
    Res s com v => mergeWith v <$> assert_total (doParse s com (next v.val))
doParse s com (ThenEmpty act next) = do
  r <- assert_total $ doParse s com act
  case r of
    Failure com fatal errs => pure $ Failure com fatal errs
    Res s com v => mergeWith v <$> assert_total (doParse s com next)
doParse s com (ThenEat act next) = do
  r <- assert_total $ doParse s com act
  case r of
    Failure com fatal errs => pure $ Failure com fatal errs
    Res s com v => mergeWith v <$> assert_total (doParse s com next)
doParse s com (Bounds act) = assert_total $ doParse s com act <&> \r => case r of
  Failure com fatal errs => Failure com fatal errs
  Res s com v => Res s com (v <$ v)
doParse s com Position = do
  (mx, pop) <- push nextToken
  pop $> case mx of
    Nothing => Failure com False (Error "End of input" Nothing ::: Nil)
    Just x => Res s com (irrelevantBounds x.bounds)
doParse s com (Act action) = pure $ Res (s <+> action) com (irrelevantBounds ())


export
parseWithM : (Monoid state, MonadToken m tok) =>
  {c : Bool} -> (parser : Grammar state tok c ty) ->
  m (Either (List1 (ParsingError tok)) (state, ty))
parseWithM p = doParse neutral False p <&> \r => case r of
  Failure _ _ errs => Left errs
  Res s _ v => Right (s, v.val)

export
parseM : (MonadToken m tok) =>
  {c : Bool} -> (parser : Grammar () tok c ty) ->
  m (Either (List1 (ParsingError tok)) ty)
parseM p = map snd <$> parseWithM p

MonadToken (State (List (WithBounds tok))) tok where
  nextToken = state $ \xs => case xs of
    (x::xs') => (xs', Just x)
    [] => ([], Nothing)

  push act = do
    xs <- get
    r <- act
    pure (r, put xs)

export
parseWith : Monoid state => {c : Bool} -> (act : Grammar state tok c ty) -> (xs : List (WithBounds tok)) ->
        Either (List1 (ParsingError tok)) (state, ty, List (WithBounds tok))
parseWith act xs
    = case runState xs $ doParse neutral False act of
           (_, Failure _ _ errs) => Left errs
           (rest, Res s _ v) => Right (s, v.val, rest)

||| Parse a list of tokens according to the given grammar. If successful,
||| returns a pair of the parse result and the unparsed tokens (the remaining
||| input).
export
parse : {c : Bool} -> (act : Grammar () tok c ty) -> (xs : List (WithBounds tok)) ->
        Either (List1 (ParsingError tok)) (ty, List (WithBounds tok))
parse act xs = parseWith act xs <&> \(_, x, rest) => (x, rest)
