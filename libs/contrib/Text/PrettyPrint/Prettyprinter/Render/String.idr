module Text.PrettyPrint.Prettyprinter.Render.String

import Data.String
import Text.PrettyPrint.Prettyprinter.Doc

%default total

export
renderString : SimpleDocStream ann -> String
renderString SEmpty = neutral
renderString (SChar c rest) = singleton c <+> renderString rest
renderString (SText l t rest) = t <+> renderString rest
renderString (SLine l rest) = singleton '\n' <+> textSpaces l <+> renderString rest
renderString (SAnnPush ann rest) = renderString rest
renderString (SAnnPop rest) = renderString rest

export
renderIO : SimpleDocStream ann -> IO ()
renderIO SEmpty = pure ()
renderIO (SChar c rest) = do putChar c; renderIO rest
renderIO (SText l t rest) = do putStr t; renderIO rest
renderIO (SLine l rest) = do putChar '\n'
                             putStr (textSpaces l)
                             renderIO rest
renderIO (SAnnPush ann rest) = renderIO rest
renderIO (SAnnPop rest) = renderIO rest

||| Prettyprints a document to standard output, using default options.
export
putDoc : Doc ann -> IO ()
putDoc = renderIO . layoutPretty defaultLayoutOptions
