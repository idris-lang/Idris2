module Text.PrettyPrint.Prettyprinter.Render.Terminal

import Data.Maybe
import Data.String
import public Control.ANSI
import Control.Monad.ST
import Text.PrettyPrint.Prettyprinter.Doc

%default covering

public export
AnsiStyle : Type
AnsiStyle = List SGR

export
color : Color -> AnsiStyle
color c = pure $ SetForeground c

export
bgColor : Color -> AnsiStyle
bgColor c = pure $ SetBackground c

export
bold : AnsiStyle
bold = pure $ SetStyle Bold

export
italic : AnsiStyle
italic = pure $ SetStyle Italic

export
underline : AnsiStyle
underline = pure $ SetStyle SingleUnderline

export
strike : AnsiStyle
strike = pure $ SetStyle Striked

export
renderString : SimpleDocStream AnsiStyle -> String
renderString sdoc = fromMaybe "<internal pretty printing error>" $ runST $ do
    styleStackRef <- newSTRef {a = List AnsiStyle} [neutral]
    outputRef <- newSTRef {a = String} neutral
    go styleStackRef outputRef sdoc
    readSTRef styleStackRef >>= \case
      [] => pure Nothing
      [_] => Just <$> readSTRef outputRef
      _ => pure Nothing
  where
    push : STRef s (List AnsiStyle) -> List SGR -> ST s ()
    push stack x = modifySTRef stack (x ::)

    peek : STRef s (List AnsiStyle) -> ST s (Maybe AnsiStyle)
    peek stack = do
      (x :: _) <- readSTRef stack | [] => pure Nothing
      pure (Just x)

    pop : STRef s (List AnsiStyle) -> ST s (Maybe AnsiStyle)
    pop stack = do
      (x :: xs) <- readSTRef stack | [] => pure Nothing
      writeSTRef stack xs
      pure (Just x)

    writeOutput : STRef s String -> String -> ST s ()
    writeOutput out x = modifySTRef out (<+> x)

    go : STRef s (List AnsiStyle) -> STRef s String -> SimpleDocStream AnsiStyle -> ST s ()
    go stack out SEmpty = pure ()
    go stack out (SChar c rest) = do
      writeOutput out (singleton c)
      go stack out rest
    go stack out (SText l t rest) = do
      writeOutput out t
      go stack out rest
    go stack out (SLine l rest) = do
      writeOutput out (singleton '\n' <+> textSpaces l)
      go stack out rest
    go stack out (SAnnPush style rest) = do
      Just currentStyle <- peek stack
        | Nothing => writeSTRef stack []
      let newStyle = style <+> currentStyle
      push stack newStyle
      writeOutput out (escapeSGR newStyle)
      go stack out rest
    go stack out (SAnnPop rest) = do
      _ <- pop stack
      Just newStyle <- peek stack
        | Nothing => writeSTRef stack []
      writeOutput out (escapeSGR (Reset :: newStyle))
      go stack out rest

export
renderIO : SimpleDocStream AnsiStyle -> IO ()
renderIO = putStrLn . renderString

export
putDoc : Doc AnsiStyle -> IO ()
putDoc = renderIO . layoutPretty defaultLayoutOptions
