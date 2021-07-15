module Libraries.Text.PrettyPrint.Prettyprinter.SimpleDocTree

import Libraries.Text.PrettyPrint.Prettyprinter.Doc
import Libraries.Text.Parser

%default total

||| Tree-like structure more suitable for rendering to a structured
||| format such as HTML.
public export
data SimpleDocTree : Type -> Type where
  STEmpty : SimpleDocTree ann
  STChar : (c : Char) -> SimpleDocTree ann
  STText : (len : Int) -> (text : String) -> SimpleDocTree ann
  STLine : (i : Int) -> SimpleDocTree ann
  STAnn : ann -> (rest : SimpleDocTree ann) -> SimpleDocTree ann
  STConcat : List (SimpleDocTree ann) -> SimpleDocTree ann

||| Changes the annotation of a document, or none at all.
export
alterAnnotationsST : (ann -> List ann') -> SimpleDocTree ann -> SimpleDocTree ann'
alterAnnotationsST re STEmpty = STEmpty
alterAnnotationsST re (STChar c) = STChar c
alterAnnotationsST re (STText len text) = STText len text
alterAnnotationsST re (STLine i) = STLine i
alterAnnotationsST re (STAnn ann rest) = foldr STAnn (alterAnnotationsST re rest) (re ann)
alterAnnotationsST re (STConcat xs) = assert_total $ STConcat (map (alterAnnotationsST re) xs)

||| Changes the annotation of a document.
export
reAnnotateST : (ann -> ann') -> SimpleDocTree ann -> SimpleDocTree ann'
reAnnotateST f = alterAnnotationsST (pure . f)

||| Removes all annotations.
export
unAnnotateST : SimpleDocTree ann -> SimpleDocTree xxx
unAnnotateST = alterAnnotationsST (const [])

||| Collects all annotations from a document.
export
collectAnnotations : Monoid m => (ann -> m) -> SimpleDocTree ann -> m
collectAnnotations f STEmpty = neutral
collectAnnotations f (STChar c) = neutral
collectAnnotations f (STText len text) = neutral
collectAnnotations f (STLine i) = neutral
collectAnnotations f (STAnn ann rest) = f ann <+> collectAnnotations f rest
collectAnnotations f (STConcat xs) = assert_total $ concat $ map (collectAnnotations f) xs

||| Transform a document based on its annotations.
export
traverse : Applicative f => (ann -> f ann') -> SimpleDocTree ann -> f (SimpleDocTree ann')
traverse f STEmpty = pure STEmpty
traverse f (STChar c) = pure $ STChar c
traverse f (STText len text) = pure $ STText len text
traverse f (STLine i) = pure $ STLine i
traverse f (STAnn ann rest) = STAnn <$> f ann <*> traverse f rest
traverse f (STConcat xs) = assert_total $ STConcat <$> Prelude.traverse (traverse f) xs

sdocToTreeParser : SimpleDocStream ann -> (Maybe (SimpleDocTree ann), Maybe (SimpleDocStream ann))
sdocToTreeParser SEmpty = (Just STEmpty, Nothing)
sdocToTreeParser (SChar c rest) = case sdocToTreeParser rest of
  (Just tree, rest') => (Just $ STConcat [STChar c, tree], rest')
  (Nothing, rest') => (Just $ STChar c, rest')
sdocToTreeParser (SText len text rest) = case sdocToTreeParser rest of
  (Just tree, rest') => (Just $ STConcat [STText len text, tree], rest')
  (Nothing, rest') => (Just $ STText len text, rest')
sdocToTreeParser (SLine i rest) = case sdocToTreeParser rest of
  (Just tree, rest') => (Just $ STConcat [STLine i, tree], rest')
  (Nothing, rest') => (Just $ STLine i, rest')
sdocToTreeParser (SAnnPush ann rest) = case sdocToTreeParser rest of
  (tree, Nothing) => (Nothing, Nothing)
  (Just tree, Nothing) => (Just $ STAnn ann tree, Nothing)
  (Just tree, Just rest') => case sdocToTreeParser rest' of
    (Just tree', rest'') => (Just $ STConcat [STAnn ann tree, tree'], rest'')
    (Nothing, rest'') => (Just $ STAnn ann tree, rest'')
  (Nothing, Just rest') => assert_total $ sdocToTreeParser rest'
  (Nothing, Nothing) => (Nothing, Nothing)
sdocToTreeParser (SAnnPop rest) = (Nothing, Just rest)

export
fromStream : SimpleDocStream ann -> SimpleDocTree ann
fromStream sdoc = case sdocToTreeParser sdoc of
    (Just tree, Nothing) => flatten tree
    _ => internalError
  where
    flatten : SimpleDocTree ann -> SimpleDocTree ann
    flatten (STConcat [x, STEmpty]) = flatten x
    flatten (STConcat [x, STConcat xs]) = case flatten (STConcat xs) of
      (STConcat xs') => STConcat (x :: xs')
      y => STConcat [x, y]
    flatten x = x

    internalError : SimpleDocTree ann
    internalError = let msg = "<internal pretty printing error>" in
                        STText (cast $ length msg) msg
