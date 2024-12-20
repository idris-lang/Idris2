module Interface

interface Show a => Pretty (0 a : Type) where
  constructor MkPretty

  0 Doc : Type
  toDoc : String -> Doc

  pretty : a -> Doc
  pretty n = toDoc (show n)

  prettys : List a -> List Doc
  prettys [] = []
  prettys (a :: as) = pretty a :: prettys as
