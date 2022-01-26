module Libraries.Text.PrettyPrint.Prettyprinter.Util

import Data.List
import Libraries.Text.PrettyPrint.Prettyprinter.Doc
import Libraries.Text.PrettyPrint.Prettyprinter.Render.String

%default total

||| Split an input into word-sized `Doc`.
export
words : String -> List (Doc ann)
words s = map pretty $ map pack (helper (unpack s))
  where
    helper : List Char -> List (List Char)
    helper s =
      case dropWhile isSpace s of
           [] => []
           s' => let (w, s'') = break isSpace s' in
                     w :: helper (assert_smaller s s'')

||| Optionally annotate a document
export
annotateM : Maybe ann -> Doc ann -> Doc ann
annotateM = maybe id annotate

||| Insert soft linebreaks between words, so that text is broken into multiple
||| lines when it exceeds the available width.
export
reflow : String -> Doc ann
reflow = fillSep . words

||| Renders a document with a certain width.
export
putDocW : Nat -> Doc ann -> IO ()
putDocW w = renderIO . layoutPretty ({ layoutPageWidth := AvailablePerLine (cast w) 1 } defaultLayoutOptions)
