||| A simple parser combinator library for strings. Inspired by attoparsec zepto.
module Data.String.Parser

import Control.Monad.Identity
import Data.Strings

%default partial

public export
record State where
    constructor S
    input : String
    pos : Int
    maxPos : Int

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
parseT : Monad m => ParseT m a -> String -> m (Either String a)
parseT p str = do res <- p.runParser (S str 0 (cast $ length str))
                  case res of
                      OK r s => pure$ Right r
                      Fail i err => pure$ Left $ fastAppend ["Parse failed at position ", show i, ": ", err]

public export
parse : Parser a ->  String -> Either String a
parse p str = runIdentity $ parseT p str

public export
satisfy : Monad m => (Char -> Bool) -> ParseT m Char
satisfy f = P $ \s => do if s.pos < s.maxPos
                            then do
                                let ch = strIndex s.input s.pos
                                if f ch
                                    then pure $ OK ch (S s.input (s.pos + 1) s.maxPos)
                                    else pure $ Fail (s.pos) "satisfy"
                            else pure $ Fail (s.pos) "satisfy"
public export
string : Monad m => String -> ParseT m ()
string str = P $ \s => do let len : Int = cast $ length str
                          if s.pos+len < s.maxPos
                              then do let head = substr (fromInteger $ cast s.pos) (length str) s.input
                                      if head == str
                                        then pure $ OK () (S s.input (s.pos + len) s.maxPos)
                                        else pure $ Fail (s.pos) ("string " ++ show str)
                              else pure $ Fail (s.pos) ("string " ++ show str)

public export
char : Monad m => Char -> ParseT m ()
char c = do _ <- satisfy (== c)
            pure ()

mutual
    public export
    some : Monad m => ParseT m a -> ParseT m (List a)
    some p = pure (!p :: !(many p))

    public export
    many : Monad m => ParseT m a -> ParseT m (List a)
    many p = some p <|> pure []

