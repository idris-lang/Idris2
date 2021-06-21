module ParseSS

import System
import System.File
import Data.String.Parser
import Control.Monad.Either

export
ichar : Monad m => Char -> ParseT m ()
ichar c = ignore $ char c

export
istring : Monad m => String -> ParseT m ()
istring c = ignore $ string c

anyChar : Applicative m => ParseT m Char
anyChar = satisfy (const True)

anyBeforeMatch : Monad m => ParseT m v -> ParseT m v
anyBeforeMatch match =
    do
      ignore $ many (requireFailure match >> ignore anyChar)
      match


parsePlusTest : Monad m => ParseT m String
parsePlusTest =
  do
    anyBeforeMatch $ istring "(define NatSpeedBug-plusNSBTest (lambda () ("
    plusNSBCalled <- many $ satisfy (/= ' ')
    istring " (NatSpeedBug-v1) (NatSpeedBug-v2))))"
    ignore $ many anyChar
    eos
    pure $ pack plusNSBCalled

parsePlusTestCalled : Applicative m => Monad m => String -> ParseT m ()
parsePlusTestCalled funcName =
  do
    anyBeforeMatch $ istring $ "(define "++funcName++" (lambda (ext-0 ext-1) (+ ext-0 ext-1)))"
    ignore $ many anyChar
    eos

parseMultTest : Monad m => ParseT m String
parseMultTest =
  do
    anyBeforeMatch $ istring "(define NatSpeedBug-multNSBTest (lambda () ("
    multNSBCalled <- many $ satisfy (/= ' ')
    istring " (PreludeC-45Types-u--fromInteger_Num_Nat 2) (NatSpeedBug-v2))))"
    ignore $ many anyChar
    eos
    pure $ pack multNSBCalled

parseMultTestCalled : Applicative m => Monad m => String -> ParseT m ()
parseMultTestCalled funcName =
  do
    anyBeforeMatch $ istring $ "(define "++funcName++" (lambda (ext-0 ext-1) (* ext-0 ext-1)))"
    ignore $ many anyChar
    eos

parse : Monad m => String -> ParseT (EitherT String m) x -> EitherT String m x
parse fd parser =
   do
     x <- map fst <$> parseT parser fd
     either left right x


main : IO ()
main =
  do
    [_,fn] <- getArgs
      | _ => putStrLn "Please specify a filename"
    Right fd <- readFile fn
      | Left e => putStrLn ("Error reading "++fn++", "++show e)

    out <-  runEitherT $ do
                putStrLn "(+) test"
                ptc <- parse fd parsePlusTest
                parse fd $ parsePlusTestCalled ptc
                putStrLn "minus test"
                parse fd $ anyBeforeMatch $ istring "(define NatSpeedBug-minusNSBTest (lambda () (PreludeC-45Types-prim__integerToNat (- (NatSpeedBug-v1) (NatSpeedBug-v2)))))"
                putStrLn "(*) test"
                mtc <- parse fd parseMultTest
                parse fd $ parseMultTestCalled mtc
                putStrLn "natToIntegerNSBTest"
                parse fd $ anyBeforeMatch $ istring "(define NatSpeedBug-natToIntegerNSBTest (lambda () (NatSpeedBug-v1)))"
                putStrLn "integerToNatNSBTest"
                parse fd $ anyBeforeMatch $ istring "(define NatSpeedBug-integerToNatNSBTest (lambda () (PreludeC-45Types-prim__integerToNat 100000000)))"

    either (\x => putStrLn $ "Error : " ++ x) (const $ putStrLn "Passed") out

