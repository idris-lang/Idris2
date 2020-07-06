||| A simple parser combinator library for strings. Inspired by attoparsec zepto.
module Data.String.Parser

import Control.Monad.Identity
import Control.Monad.Trans

import Data.Strings

%default partial

||| The input state, pos is position in the string and maxPos is the length of the input string.
public export
record State where
    constructor S
    input : String
    pos : Int
    maxPos : Int

Show State where
    show s = "(" ++ show s.input ++", " ++ show s.pos ++ ", " ++ show s.maxPos ++")"

||| Result of applying a parser
public export
data Result a = Fail Int String | OK a State


public export
record ParseT (m : Type -> Type) (a : Type) where
    constructor P
    runParser : State -> m (Result a)

public export
Parser : Type -> Type
Parser a = ParseT Identity a

public export
implementation Monad m => Functor (ParseT m) where
    map f p = P $ \state =>
         do res <- p.runParser state
            case res of
                OK r state' => pure (OK (f r) state')
                Fail i err => pure (Fail i err)

public export
Monad m => Applicative (ParseT m) where
    pure x = P $ \s => pure (OK x s)
    f <*> x = P $ \s => case !(x.runParser s) of
                            OK r s' => case !(f.runParser s') of
                                            OK f' fs => pure (OK (f' r) fs)
                                            Fail i err => pure (Fail i err)
                            Fail i err => pure (Fail i err)

public export
Monad m => Monad (ParseT m) where
    m >>= k = P $ \state =>
        do res <- m.runParser state
           case res of
                OK a state' => (k a).runParser state'
                Fail i err => pure (Fail i err)

public export
Monad m => Alternative (ParseT m) where
    empty = P $ \s => pure $ Fail (s.pos) "no alternative left"
    a <|> b = P $ \s => case !(a.runParser s) of
                            OK r s' => pure $ OK r s'
                            Fail _ _ => b.runParser s

public export
MonadTrans ParseT where
    lift x = P $ \s => do res <-x
                          pure $ OK res s

||| Run a parser in a monad
||| Returns a tuple of the result and final position on success.
||| Returns an error message on failure.
export
parseT : Monad m => ParseT m a -> String -> m (Either String (a, Int))
parseT p str = do res <- p.runParser (S str 0 (strLength str))
                  case res of
                      OK r s => pure $ Right (r, s.pos)
                      Fail i err => pure $ Left $ fastAppend ["Parse failed at position ", show i, ": ", err]

||| Run a parser in a pure function
||| Returns a tuple of the result and final position on success.
||| Returns an error message on failure.
export
parse : Parser a -> String -> Either String (a, Int)
parse p str = runIdentity $ parseT p str

||| Combinator that replaces the error message on failure.
||| This allows combinators to output relevant errors
export
(<?>) : Monad m => ParseT m a -> String -> ParseT m a
(<?>) p msg = P $ \s => case !(p.runParser s) of
                            OK r s' => pure $ OK r s'
                            Fail i _ => pure $ Fail i msg

infixl 0 <?>

||| Succeeds if the next char satisfies the predicate `f`
export
satisfy : Monad m => (Char -> Bool) -> ParseT m Char
satisfy f = P $ \s => do if s.pos < s.maxPos
                            then do
                                let ch = strIndex s.input s.pos
                                if f ch
                                    then pure $ OK ch (S s.input (s.pos + 1) s.maxPos)
                                    else pure $ Fail (s.pos) "satisfy"
                            else pure $ Fail (s.pos) "satisfy"

||| Succeeds if the string `str` follows.
export
string : Monad m => String -> ParseT m ()
string str = P $ \s => do let len = strLength str
                          if s.pos+len <= s.maxPos
                              then do let head = strSubstr s.pos len s.input
                                      if head == str
                                        then pure $ OK () (S s.input (s.pos + len) s.maxPos)
                                        else pure $ Fail (s.pos) ("string " ++ show str)
                              else pure $ Fail (s.pos) ("string " ++ show str)

||| Succeeds if the next char is `c`
export
char : Monad m => Char -> ParseT m ()
char c = do _ <- satisfy (== c)
            pure ()

mutual
    ||| Succeeds if `p` succeeds, will continue to match `p` until it fails
    ||| and accumulate the results in a list
    export
    some : Monad m => ParseT m a -> ParseT m (List a)
    some p = pure (!p :: !(many p))

    ||| Always succeeds, will accumulate the results of `p` in a list until it fails.
    export
    many : Monad m => ParseT m a -> ParseT m (List a)
    many p = some p <|> pure []

||| Always succeeds, applies the predicate `f` on chars until it fails and creates a string
||| from the results.
export
takeWhile : Monad m => (Char -> Bool) -> ParseT m String
takeWhile f = do ls <- many (satisfy f)
                 pure $ pack ls

||| Returns the result of the parser `p` or `def` if it fails.
export
option : Monad m => a -> ParseT m a -> ParseT m a
option def p = p <|> pure def

||| Returns a Maybe that contains the result of `p` if it succeeds or `Nothing` if it fails.
export
optional : Monad m => ParseT m a -> ParseT m (Maybe a)
optional p = (p >>= \res => pure $ Just res) <|> pure Nothing
