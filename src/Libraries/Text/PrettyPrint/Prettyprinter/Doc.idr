module Libraries.Text.PrettyPrint.Prettyprinter.Doc

import Data.List
import public Data.List1
import Data.Maybe
import Data.SnocList
import Data.String
import public Libraries.Data.Span
import Libraries.Data.String.Extra

%default total

export
textSpaces : Int -> String
textSpaces n = String.replicate (integerToNat $ cast n) ' '

||| Maximum number of characters that fit in one line.
public export
data PageWidth : Type where
  ||| The `Int` is the number of characters, including whitespace, that fit in a line.
  ||| The `Double` is the ribbon, the fraction of the toal page width that can be printed on.
  AvailablePerLine : Int -> Double -> PageWidth
  ||| The layouters should not introduce line breaks.
  Unbounded : PageWidth

data FlattenResult : Type -> Type where
  Flattened : a -> FlattenResult a
  AlreadyFlat : FlattenResult a
  NeverFlat : FlattenResult a

Functor FlattenResult where
  map f (Flattened a) = Flattened (f a)
  map _ AlreadyFlat = AlreadyFlat
  map _ NeverFlat = NeverFlat

||| Fusion depth parameter.
public export
data FusionDepth : Type where
  ||| Do not dive deep into nested documents.
  Shallow : FusionDepth
  ||| Recurse into all parts of the `Doc`. May impact performace.
  Deep : FusionDepth

||| This data type represents pretty documents that have
||| been annotated with an arbitrary data type `ann`.
public export
data Doc : Type -> Type where
  Empty : Doc ann
  Chara : (c : Char) -> Doc ann                         -- Invariant: not '\n'
  Text : (len : Int) -> (text : String) -> Doc ann      -- Invariant: at least two characters long and no '\n'
  Line : Doc ann
  FlatAlt : Lazy (Doc ann) -> Lazy (Doc ann) -> Doc ann
  Cat : Doc ann -> Doc ann -> Doc ann
  Nest : (i : Int) -> Doc ann -> Doc ann
  Union : Lazy (Doc ann) -> Lazy (Doc ann) -> Doc ann   -- Invariant: the first line of the first document should be
                                                        -- longer than the first lines of the second one
  Column : (Int -> Doc ann) -> Doc ann
  WithPageWidth : (PageWidth -> Doc ann) -> Doc ann
  Nesting : (Int -> Doc ann) -> Doc ann
  Annotated : ann -> Doc ann -> Doc ann

export
Semigroup (Doc ann) where
  (<+>) = Cat

export
Monoid (Doc ann) where
  neutral = Empty

||| Layout a document depending on which column it starts at.
export
column : (Int -> Doc ann) -> Doc ann
column = Column

||| Lays out a document with the current nesting level increased by `i`.
export
nest : Int -> Doc ann -> Doc ann
nest 0 x = x
nest i x = Nest i x

||| Layout a document depending on the current nesting level.
export
nesting : (Int -> Doc ann) -> Doc ann
nesting = Nesting

||| Lays out a document, and makes the column width of it available to a function.
export
width : Doc ann -> (Int -> Doc ann) -> Doc ann
width doc f = column (\colStart => doc <+> column (\colEnd => f (colEnd - colStart)))

||| Layout a document depending on the page width, if one has been specified.
export
pageWidth : (PageWidth -> Doc ann) -> Doc ann
pageWidth = WithPageWidth

||| Lays out a document with the nesting level set to the current column.
export
align : Doc ann -> Doc ann
align d = column (\k => nesting (\i => nest (k - i) d))

||| Lays out a document with a nesting level set to the current column plus `i`.
||| Negative values are allowed, and decrease the nesting level accordingly.
export
hang : Int -> Doc ann -> Doc ann
hang i d = align (nest i d)

||| Insert a number of spaces.
export
spaces : Int -> Doc ann
spaces n = if n <= 0
              then Empty
              else if n == 1
                      then Chara ' '
                      else Text n (textSpaces n)

||| Indents a document with `i` spaces, starting from the current cursor position.
export
indent : Int -> Doc ann -> Doc ann
indent i d = hang i (spaces i <+> d)

||| Lays out a document. It then appends spaces until the width is equal to `i`.
||| If the width is already larger, nothing is appended.
export
fill : Int -> Doc ann -> Doc ann
fill n doc = width doc (\w => spaces $ n - w)

infixr 6 <++>
||| Concatenates two documents with a space in between.
export
(<++>) : Doc ann -> Doc ann -> Doc ann
x <++> y = x <+> Chara ' ' <+> y

||| The empty document behaves like `pretty ""`, so it has a height of 1.
export
emptyDoc : Doc ann
emptyDoc = Empty

||| Behaves like `space` if the resulting output fits the page, otherwise like `line`.
export
softline : Doc ann
softline = Union (Chara ' ') Line

||| Like `softline`, but behaves like `neutral` if the resulting output does not fit
||| on the page.
export
softline' : Doc ann
softline' = Union neutral Line

||| A line break, even when grouped.
export
hardline : Doc ann
hardline = Line

flatten : Doc ann -> Doc ann
flatten Empty = Empty
flatten (Chara x) = Chara x
flatten (Text len x) = Text len x
flatten Line = Empty
flatten (FlatAlt _ y) = flatten y
flatten (Cat x y) = Cat (flatten x) (flatten y)
flatten (Nest i x) = Nest i (flatten x)
flatten (Union x _) = flatten x
flatten (Column f) = Column (\x => flatten $ f x)
flatten (WithPageWidth f) = WithPageWidth (\x => flatten $ f x)
flatten (Nesting f) = Nesting (\x => flatten $ f x)
flatten (Annotated ann x) = Annotated ann (flatten x)

changesUponFlattening : Doc ann -> FlattenResult (Doc ann)
changesUponFlattening Empty = AlreadyFlat
changesUponFlattening (Chara x) = AlreadyFlat
changesUponFlattening (Text x y) = AlreadyFlat
changesUponFlattening Line = NeverFlat
changesUponFlattening (FlatAlt _ y) = Flattened (flatten y)
changesUponFlattening (Cat x y) = case (changesUponFlattening x, changesUponFlattening y) of
  (NeverFlat, _) => NeverFlat
  (_, NeverFlat) => NeverFlat
  (Flattened x', Flattened y') => Flattened (Cat x' y')
  (Flattened x', AlreadyFlat) => Flattened (Cat x' y)
  (AlreadyFlat , Flattened y') => Flattened (Cat x y')
  (AlreadyFlat , AlreadyFlat) => AlreadyFlat
changesUponFlattening (Nest i x) = map (Nest i) (changesUponFlattening x)
changesUponFlattening (Union x _) = Flattened x
changesUponFlattening (Column f) = Flattened (Column (flatten . f))
changesUponFlattening (WithPageWidth f) = Flattened (WithPageWidth (flatten . f))
changesUponFlattening (Nesting f) = Flattened (Nesting (flatten . f))
changesUponFlattening (Annotated ann x) = map (Annotated ann) (changesUponFlattening x)

||| Tries laying out a document into a single line by removing the contained
||| line breaks; if this does not fit the page, or has an `hardline`, the document
||| is laid out without changes.
export
group : Doc ann -> Doc ann
group (Union x y) = Union x y
group (FlatAlt x y) = case changesUponFlattening y of
  Flattened y' => Union y' x
  AlreadyFlat => Union y x
  NeverFlat => x
group x = case changesUponFlattening x of
  Flattened x' => Union x' x
  AlreadyFlat => x
  NeverFlat => x

||| By default renders the first document, When grouped renders the second, with
||| the first as fallback when there is not enough space.
export
flatAlt : Lazy (Doc ann) -> Lazy (Doc ann) -> Doc ann
flatAlt = FlatAlt

||| Advances to the next line and indents to the current nesting level.
export
line : Doc ann
line = FlatAlt Line (Chara ' ')

||| Like `line`, but behaves like `neutral` if the line break is undone by `group`.
export
line' : Doc ann
line' = FlatAlt Line Empty

||| First lays out the document. It then appends spaces until the width is equal to `i`.
||| If the width is already larger than `i`, the nesting level is decreased by `i`
||| and a line is appended.
export
fillBreak : Int -> Doc ann -> Doc ann
fillBreak f x  = width x (\w => if w > f
                                   then nest f line'
                                   else spaces $ f - w)

||| Concatenate all documents element-wise with a binary function.
export
concatWith : (Doc ann -> Doc ann -> Doc ann) -> List (Doc ann) -> Doc ann
concatWith f [] = neutral
concatWith f (x :: xs) = foldl f x xs

||| Concatenates all documents horizontally with `(<++>)`.
export
hsep : List (Doc ann) -> Doc ann
hsep = concatWith (<++>)

||| Concatenates all documents above each other. If a `group` undoes the line breaks,
||| the documents are separated with a space instead.
export
vsep : List (Doc ann) -> Doc ann
vsep = concatWith (\x, y => x <+> line <+> y)

||| Concatenates the documents horizontally with `(<++>)` as long as it fits the page,
||| then inserts a line and continues.
export
fillSep : List (Doc ann) -> Doc ann
fillSep = concatWith (\x, y => x <+> softline <+> y)

||| Tries laying out the documents separated with spaces and if this does not fit,
||| separates them with newlines.
export
sep : List (Doc ann) -> Doc ann
sep = group . vsep

||| Concatenates all documents horizontally with `(<+>)`.
export
hcat : List (Doc ann) -> Doc ann
hcat = concatWith (<+>)

||| Vertically concatenates the documents. If it is grouped, the line breaks are removed.
export
vcat : List (Doc ann) -> Doc ann
vcat = concatWith (\x, y => x <+> line' <+> y)

||| Concatenates documents horizontally with `(<+>)` as log as it fits the page, then
||| inserts a line and continues.
export
fillCat : List (Doc ann) -> Doc ann
fillCat = concatWith (\x, y => x <+> softline' <+> y)

||| Tries laying out the documents separated with nothing, and if it does not fit the page,
||| separates them with newlines.
export
cat : List (Doc ann) -> Doc ann
cat = group . vcat

||| Appends `p` to all but the last document.
export
punctuate : Doc ann -> List (Doc ann) -> List (Doc ann)
punctuate _ [] = []
punctuate _ [d] = [d]
punctuate p (d :: ds) = (d <+> p) :: punctuate p ds

export
plural : (Num amount, Eq amount) => doc -> doc -> amount -> doc
plural one multiple n = if n == 1 then one else multiple

||| Encloses the document between two other documents using `(<+>)`.
export
enclose : Doc ann -> Doc ann -> Doc ann -> Doc ann
enclose l r x = l <+> x <+> r

||| Reordering of `encloses`.
||| Example: concatWith (surround (pretty ".")) [pretty "Text", pretty "PrettyPrint", pretty "Doc"]
|||          Text.PrettyPrint.Doc
export
surround : Doc ann -> Doc ann -> Doc ann -> Doc ann
surround x l r = l <+> x <+> r

||| Concatenates the documents separated by `s` and encloses the resulting document by `l` and `r`.
export
encloseSep : Doc ann -> Doc ann -> Doc ann -> List (Doc ann) -> Doc ann
encloseSep l r s []  = l <+> r
encloseSep l r s [d] = l <+> d <+> r
encloseSep l r s ds  = cat (zipWith (<+>) (l :: replicate (length ds `minus` 1) s) ds) <+> r

unsafeTextWithoutNewLines : String -> Doc ann
unsafeTextWithoutNewLines str = case strM str of
  StrNil => Empty
  StrCons c cs => if cs == ""
                     then Chara c
                     else Text (cast $ length str) str

||| Adds an annotation to a document.
export
annotate : ann -> Doc ann -> Doc ann
annotate = Annotated

||| Changes the annotations of a document. Individual annotations can be removed,
||| changed, or replaced by multiple ones.
export
alterAnnotations : (ann -> List ann') -> Doc ann -> Doc ann'
alterAnnotations re Empty = Empty
alterAnnotations re (Chara c) = Chara c
alterAnnotations re (Text l t) = Text l t
alterAnnotations re Line = Line
alterAnnotations re (FlatAlt x y) = FlatAlt (alterAnnotations re x) (alterAnnotations re y)
alterAnnotations re (Cat x y) = Cat (alterAnnotations re x) (alterAnnotations re y)
alterAnnotations re (Nest i x) = Nest i (alterAnnotations re x)
alterAnnotations re (Union x y) = Union (alterAnnotations re x) (alterAnnotations re y)
alterAnnotations re (Column f) = Column (\x => alterAnnotations re $ f x)
alterAnnotations re (WithPageWidth f) = WithPageWidth (\x => alterAnnotations re $ f x)
alterAnnotations re (Nesting f) = Nesting (\x => alterAnnotations re $ f x)
alterAnnotations re (Annotated ann x) = foldr Annotated (alterAnnotations re x) (re ann)

||| Removes all annotations.
export
unAnnotate : Doc ann -> Doc xxx
unAnnotate = alterAnnotations (const [])

||| Changes the annotations of a document.
export
reAnnotate : (ann -> ann') -> Doc ann -> Doc ann'
reAnnotate re = alterAnnotations (pure . re)

||| Alter the document's annotations.
export
Functor Doc where
  map = reAnnotate

||| Overloaded conversion to `Doc`.
||| @ ann is the type of annotations
||| @ a   is the type of things that can be prettified
||| We declare that only `a` is relevant when looking for an implementation
|||
||| Pro tips:
||| 1. use `prettyBy` if a subprinter uses a different type of annotations
||| 2. use a variable `ann` rather than `Void` if no annnotation is needed
|||    (to avoid needless calls to `prettyBy absurd`)
public export
interface Pretty ann a | a where
  pretty : a -> Doc ann
  pretty x = prettyPrec Open x

  prettyPrec : Prec -> a -> Doc ann
  prettyPrec _ x = pretty x

||| Sometimes we want to call a subprinter that uses a different annotation
||| type. That's fine as long as we know how to embed such annotations into
||| the target ones.
||| @ ann1 is the type of annotations used by the subprinter
||| @ ann2 is the type of annotations used in the current document
||| @ inj  explains how to inject the first into the second
export
prettyBy : Pretty ann1 a => (inj : ann1 -> ann2) -> a -> Doc ann2
prettyBy inj a = reAnnotate inj (pretty a)


||| Sometimes we want to use a document that uses no annotation whatsoever.
||| This should be equivalent to `reAnnotate absurd`, except that in this
||| case we do not traverse the document because it should be impossible to
||| manufacture an annotation of type Void.
export
Cast (Doc Void) (Doc ann) where
  cast = believe_me


||| Sometimes we want to call a subprinter that uses no annotation whatsoever.
||| This should be equivalent to `prettyBy absurd`, except that in this case
||| we do not traverse the document because it should be impossible to manufacture
||| an annotation of type Void.
export
pretty0 : Pretty Void a => a -> Doc ann
pretty0 x = cast (pretty x)

export
Pretty Void String where
  pretty str = let str' = if "\n" `isSuffixOf` str then dropLast 1 str else str in
                   vsep $ map unsafeTextWithoutNewLines $ lines str'

export
byShow : Show a => a -> Doc ann
byShow = pretty0 . show

export
FromString (Doc ann) where
  fromString = pretty0

||| Variant of `encloseSep` with braces and comma as separator.
export
list : List (Doc ann) -> Doc ann
list = group . encloseSep (flatAlt (pretty0 "[ ") (pretty0 "["))
                          (flatAlt (pretty0 " ]") (pretty0 "]"))
                          (pretty0 ", ")

||| Variant of `encloseSep` with parentheses and comma as separator.
export
tupled : List (Doc ann) -> Doc ann
tupled = group . encloseSep (flatAlt (pretty0 "( ") (pretty0 "("))
                            (flatAlt (pretty0 " )") (pretty0 ")"))
                            (pretty0 ", ")

export
prettyList : Pretty ann a => List a -> Doc ann
prettyList = align . list . map pretty

export
prettyList1 : Pretty ann a => List1 a -> Doc ann
prettyList1 = prettyList . forget

export
[prettyListMaybe] Pretty ann a => Pretty ann (List (Maybe a)) where
  pretty = prettyList . catMaybes

export
Pretty Void Char where
  pretty '\n' = line
  pretty c = Chara c

export
prettyMaybe : Pretty ann a => Maybe a -> Doc ann
prettyMaybe = maybe neutral pretty

||| Combines text nodes so they can be rendered more efficiently.
export
fuse : FusionDepth -> Doc ann -> Doc ann
fuse depth (Cat Empty x) = fuse depth x
fuse depth (Cat x Empty) = fuse depth x
fuse depth (Cat (Chara c1) (Chara c2)) = Text 2 (strCons c1 (strCons c2 ""))
fuse depth (Cat (Text lt t) (Chara c)) = Text (lt + 1) (t ++ singleton c)
fuse depth (Cat (Chara c) (Text lt t)) = Text (lt + 1) (strCons c t)
fuse depth (Cat (Text l1 t1) (Text l2 t2)) = Text (l1 + l2) (t1 ++ t2)
fuse depth (Cat (Chara x) (Cat (Chara y) z)) =
  let sub = Text 2 (strCons x (strCons y "")) in
      fuse depth $ assert_smaller (Cat (Chara x) (Cat (Chara y) z)) (Cat sub z)
fuse depth (Cat (Text lx x) (Cat (Chara y) z)) =
  let sub = Text (lx + 1) (x ++ singleton y) in
      fuse depth $ assert_smaller (Cat (Text lx x) (Cat (Chara y) z)) (Cat sub z)
fuse depth (Cat (Chara x) (Cat (Text ly y) z)) =
  let sub = Text (ly + 1) (strCons x y) in
      fuse depth $ assert_smaller (Cat (Chara x) (Cat (Text ly y) z)) (Cat sub z)
fuse depth (Cat (Text lx x) (Cat (Text ly y) z)) =
  let sub = Text (lx + ly) (x ++ y) in
      fuse depth $ assert_smaller (Cat (Text lx x) (Cat (Text ly y) z)) (Cat sub z)
fuse depth (Cat (Cat x (Chara y)) z) =
  let sub = fuse depth (Cat (Chara y) z) in
      assert_total $ fuse depth (Cat x sub)
fuse depth (Cat (Cat x (Text ly y)) z) =
  let sub = fuse depth (Cat (Text ly y) z) in
      assert_total $ fuse depth (Cat x sub)
fuse depth (Cat x y) = Cat (fuse depth x) (fuse depth y)
fuse depth (Nest i (Nest j x)) = fuse depth $ assert_smaller (Nest i (Nest j x)) (Nest (i + j) x)
fuse depth (Nest _ Empty) = Empty
fuse depth (Nest _ (Text lx x)) = Text lx x
fuse depth (Nest _ (Chara x)) = Chara x
fuse depth (Nest 0 x) = fuse depth x
fuse depth (Nest i x) = Nest i (fuse depth x)
fuse depth (Annotated ann x) = Annotated ann (fuse depth x)
fuse depth (FlatAlt x y) = FlatAlt (fuse depth x) (fuse depth y)
fuse depth (Union x y) = Union (fuse depth x) (fuse depth y)
fuse Shallow (Column f) = Column f
fuse depth (Column f) = Column (\x => fuse depth $ f x)
fuse Shallow (WithPageWidth f) = WithPageWidth f
fuse depth (WithPageWidth f) = WithPageWidth (\x => fuse depth $ f x)
fuse Shallow (Nesting f) = Nesting f
fuse depth (Nesting f) = Nesting (\x => fuse depth $ f x)
fuse depth x = x

||| This data type represents laid out documents and is used by the display functions.
public export
data SimpleDocStream : Type -> Type where
  SEmpty : SimpleDocStream ann
  SChar : (c : Char) -> (rest : Lazy (SimpleDocStream ann)) -> SimpleDocStream ann
  SText : (len : Int) -> (text : String) -> (rest : Lazy (SimpleDocStream ann)) -> SimpleDocStream ann
  SLine : (i : Int) -> (rest : SimpleDocStream ann) -> SimpleDocStream ann
  SAnnPush : ann -> (rest : SimpleDocStream ann) -> SimpleDocStream ann
  SAnnPop : (rest : SimpleDocStream ann) -> SimpleDocStream ann

internalError : SimpleDocStream ann
internalError = let msg = "<internal pretty printing error>" in
                    SText (cast $ length msg) msg SEmpty

data AnnotationRemoval = Remove | DontRemove

||| Changes the annotation of a document to a different annotation or none.
export
alterAnnotationsS : (ann -> Maybe ann') -> SimpleDocStream ann -> SimpleDocStream ann'
alterAnnotationsS re = fromMaybe internalError . go []
  where
    go : List AnnotationRemoval -> SimpleDocStream ann -> Maybe (SimpleDocStream ann')
    go stack SEmpty = pure SEmpty
    go stack (SChar c rest) = SChar c . delay <$> go stack rest
    go stack (SText l t rest) = SText l t . delay <$> go stack rest
    go stack (SLine l rest) = SLine l <$> go stack rest
    go stack (SAnnPush ann rest) = case re ann of
      Nothing => go (Remove :: stack) rest
      Just ann' => SAnnPush ann' <$> go (DontRemove :: stack) rest
    go stack (SAnnPop rest) = case stack of
      [] => Nothing
      DontRemove :: stack' => SAnnPop <$> go stack' rest
      Remove :: stack' => go stack' rest

||| Removes all annotations.
export
unAnnotateS : SimpleDocStream ann -> SimpleDocStream xxx
unAnnotateS SEmpty = SEmpty
unAnnotateS (SChar c rest) = SChar c (unAnnotateS rest)
unAnnotateS (SText l t rest) = SText l t (unAnnotateS rest)
unAnnotateS (SLine l rest) = SLine l (unAnnotateS rest)
unAnnotateS (SAnnPush ann rest) = unAnnotateS rest
unAnnotateS (SAnnPop rest) = unAnnotateS rest

||| Changes the annotation of a document.
export
reAnnotateS : (ann -> ann') -> SimpleDocStream ann -> SimpleDocStream ann'
reAnnotateS re SEmpty = SEmpty
reAnnotateS re (SChar c rest) = SChar c (reAnnotateS re rest)
reAnnotateS re (SText l t rest) = SText l t (reAnnotateS re rest)
reAnnotateS re (SLine l rest) = SLine l (reAnnotateS re rest)
reAnnotateS re (SAnnPush ann rest) = SAnnPush (re ann) (reAnnotateS re rest)
reAnnotateS re (SAnnPop rest) = SAnnPop (reAnnotateS re rest)

export
Functor SimpleDocStream where
  map = reAnnotateS

||| Collects all annotations from a document.
export
collectAnnotations : Monoid m => (ann -> m) -> SimpleDocStream ann -> m
collectAnnotations f SEmpty = neutral
collectAnnotations f (SChar c rest) = collectAnnotations f rest
collectAnnotations f (SText l t rest) = collectAnnotations f rest
collectAnnotations f (SLine l rest) = collectAnnotations f rest
collectAnnotations f (SAnnPush ann rest) = f ann <+> collectAnnotations f rest
collectAnnotations f (SAnnPop rest) = collectAnnotations f rest

||| Transform a document based on its annotations.
export
traverse : Applicative f => (ann -> f ann') -> SimpleDocStream ann -> f (SimpleDocStream ann')
traverse f SEmpty = pure SEmpty
traverse f (SChar c rest) = SChar c . delay <$> traverse f rest
traverse f (SText l t rest) = SText l t . delay <$> traverse f rest
traverse f (SLine l rest) = SLine l <$> traverse f rest
traverse f (SAnnPush ann rest) = SAnnPush <$> f ann <*> traverse f rest
traverse f (SAnnPop rest) = SAnnPop <$> traverse f rest

data WhitespaceStrippingState = AnnotationLevel Int | RecordedWithespace (List Int) Int

dropWhileEnd : (a -> Bool) -> List a -> List a
dropWhileEnd p = foldr (\x, xs => if p x && isNil xs then [] else x :: xs) []

||| Removes all trailing space characters.
export
removeTrailingWhitespace : SimpleDocStream ann -> SimpleDocStream ann
removeTrailingWhitespace = fromMaybe internalError . go (RecordedWithespace [] 0)
  where
    prependEmptyLines : List Int -> SimpleDocStream ann -> SimpleDocStream ann
    prependEmptyLines is sds0 = foldr (\_, sds => SLine 0 sds) sds0 is

    commitWhitespace : List Int -> Int -> SimpleDocStream ann -> SimpleDocStream ann
    commitWhitespace [] 0 sds = sds
    commitWhitespace [] 1 sds = SChar ' ' sds
    commitWhitespace [] n sds = SText n (textSpaces n) sds
    commitWhitespace (i :: is) n sds = prependEmptyLines is (SLine (i + n) sds)

    go : WhitespaceStrippingState -> SimpleDocStream ann -> Maybe (SimpleDocStream ann)
    go (AnnotationLevel _) SEmpty = pure SEmpty
    go l@(AnnotationLevel _) (SChar c rest) = SChar c . delay <$> go l rest
    go l@(AnnotationLevel _) (SText lt text rest) = SText lt text . delay <$> go l rest
    go l@(AnnotationLevel _) (SLine i rest) = SLine i <$> go l rest
    go (AnnotationLevel l) (SAnnPush ann rest) = SAnnPush ann <$> go (AnnotationLevel (l + 1)) rest
    go (AnnotationLevel l) (SAnnPop rest) =
      if l > 1
         then SAnnPop <$> go (AnnotationLevel (l - 1)) rest
         else SAnnPop <$> go (RecordedWithespace [] 0) rest
    go (RecordedWithespace _ _) SEmpty = pure SEmpty
    go (RecordedWithespace lines spaces) (SChar ' ' rest) = go (RecordedWithespace lines (spaces + 1)) rest
    go (RecordedWithespace lines spaces) (SChar c rest) =
      do rest' <- go (RecordedWithespace [] 0) rest
         pure $ commitWhitespace lines spaces (SChar c rest')
    go (RecordedWithespace lines spaces) (SText l text rest) =
      let stripped = pack $ dropWhileEnd (== ' ') $ unpack text
          strippedLength = cast $ length stripped
          trailingLength = l - strippedLength in
          if strippedLength == 0
             then go (RecordedWithespace lines (spaces + l)) rest
             else do rest' <- go (RecordedWithespace [] trailingLength) rest
                     pure $ commitWhitespace lines spaces (SText strippedLength stripped rest')
    go (RecordedWithespace lines spaces) (SLine i rest) = go (RecordedWithespace (i :: lines) 0) rest
    go (RecordedWithespace lines spaces) (SAnnPush ann rest) =
      do rest' <- go (AnnotationLevel 1) rest
         pure $ commitWhitespace lines spaces (SAnnPush ann rest')
    go (RecordedWithespace lines spaces) (SAnnPop _) = Nothing

public export
FittingPredicate : Type -> Type
FittingPredicate ann = Int -> Int -> Maybe Int -> SimpleDocStream ann -> Bool

data LayoutPipeline ann = Nil | Cons Int (Doc ann) (LayoutPipeline ann) | UndoAnn (LayoutPipeline ann)

export
defaultPageWidth : PageWidth
defaultPageWidth = AvailablePerLine 80 1

round : Double -> Int
round x = if x > 0
             then if x - floor x < 0.5 then cast $ floor x else cast $ ceiling x
             else if ceiling x - x < 0.5 then cast $ ceiling x else cast $ floor x

||| The remaining width on the current line.
remainingWidth : Int -> Double -> Int -> Int -> Int
remainingWidth lineLength ribbonFraction lineIndent currentColumn =
  let columnsLeftInLine = lineLength - currentColumn
      ribbonWidth = (max 0 . min lineLength . round) (cast lineLength * ribbonFraction)
      columnsLeftInRibbon = lineIndent + ribbonWidth - currentColumn in
      min columnsLeftInLine columnsLeftInRibbon

public export
record LayoutOptions where
  constructor MkLayoutOptions
  layoutPageWidth : PageWidth

export
defaultLayoutOptions : LayoutOptions
defaultLayoutOptions = MkLayoutOptions defaultPageWidth

||| The Wadler/Leijen layout algorithm.
export
layoutWadlerLeijen : FittingPredicate ann -> PageWidth -> Doc ann -> SimpleDocStream ann
layoutWadlerLeijen fits pageWidth_ doc = best 0 0 (Cons 0 doc Nil)
  where
    initialIndentation : SimpleDocStream ann -> Maybe Int
    initialIndentation (SLine i _) = Just i
    initialIndentation (SAnnPush _ s) = initialIndentation s
    initialIndentation (SAnnPop s) = initialIndentation s
    initialIndentation _ = Nothing

    selectNicer : Int -> Int -> SimpleDocStream ann -> Lazy (SimpleDocStream ann) -> SimpleDocStream ann
    selectNicer lineIndent currentColumn x y =
      if fits lineIndent currentColumn (initialIndentation y) x then x else y

    best : Int -> Int -> LayoutPipeline ann -> SimpleDocStream ann
    best _ _ Nil = SEmpty
    best nl cc (UndoAnn ds) = SAnnPop (best nl cc ds)
    best nl cc (Cons i Empty ds) = best nl cc ds
    best nl cc (Cons i (Chara c) ds) = SChar c (best nl (cc + 1) ds)
    best nl cc (Cons i (Text l t) ds) = SText l t (best nl (cc + l) ds)
    best nl cc (Cons i Line ds) = let x = best i i ds
                                      i' = case x of
                                                SEmpty => 0
                                                SLine _ _ => 0
                                                _ => i in
                                      SLine i' x
    best nl cc c@(Cons i (FlatAlt x y) ds) = best nl cc $ assert_smaller c (Cons i x ds)
    best nl cc (Cons i (Cat x y) ds) = assert_total $ best nl cc (Cons i x (Cons i y ds))
    best nl cc c@(Cons i (Nest j x) ds) = best nl cc $ assert_smaller c (Cons (i + j) x ds)
    best nl cc c@(Cons i (Union x y) ds) = let x' = best nl cc $ assert_smaller c (Cons i x ds)
                                               y' = delay $ best nl cc $ assert_smaller c (Cons i y ds) in
                                               selectNicer nl cc x' y'
    best nl cc c@(Cons i (Column f) ds) = best nl cc $ assert_smaller c (Cons i (f cc) ds)
    best nl cc c@(Cons i (WithPageWidth f) ds) = best nl cc $ assert_smaller c (Cons i (f pageWidth_) ds)
    best nl cc c@(Cons i (Nesting f) ds) = best nl cc $ assert_smaller c (Cons i (f i) ds)
    best nl cc c@(Cons i (Annotated ann x) ds) = SAnnPush ann $ best nl cc $ assert_smaller c (Cons i x (UndoAnn ds))

||| Layout a document with unbounded page width.
export
layoutUnbounded : Doc ann -> SimpleDocStream ann
layoutUnbounded = layoutWadlerLeijen (\_, _, _, sdoc => True) Unbounded

fits : Int -> SimpleDocStream ann -> Bool
fits w s = if w < 0 then False
  else case s of
            SEmpty => True
            SChar _ x => fits (w - 1) x
            SText l _ x => fits (w - l) x
            SLine i x => True
            SAnnPush _ x => fits w x
            SAnnPop x => fits w x

||| The default layout algorithm.
export
layoutPretty : LayoutOptions -> Doc ann -> SimpleDocStream ann
layoutPretty (MkLayoutOptions pageWidth_@(AvailablePerLine lineLength ribbonFraction)) =
    layoutWadlerLeijen (\lineIndent, currentColumn, _, sdoc =>
      fits (remainingWidth lineLength ribbonFraction lineIndent currentColumn) sdoc) pageWidth_
layoutPretty (MkLayoutOptions Unbounded) = layoutUnbounded

||| Layout algorithm with more lookahead than layoutPretty.
export
layoutSmart : LayoutOptions -> Doc ann -> SimpleDocStream ann
layoutSmart (MkLayoutOptions pageWidth_@(AvailablePerLine lineLength ribbonFraction)) =
    layoutWadlerLeijen fits pageWidth_
  where
    fits : Int -> Int -> Maybe Int -> SimpleDocStream ann -> Bool
    fits lineIndent currentColumn initialIndentY sdoc = go availableWidth sdoc
      where
        availableWidth : Int
        availableWidth = remainingWidth lineLength ribbonFraction lineIndent currentColumn

        minNestingLevel : Int
        minNestingLevel = case initialIndentY of
                               Just i => min i currentColumn
                               Nothing => currentColumn

        go : Int -> SimpleDocStream ann -> Bool
        go w s = if w < 0
          then False
          else case s of
                    SEmpty => True
                    SChar _ x => go (w - 1) $ assert_smaller s x
                    SText l _ x => go (w - l) $ assert_smaller s x
                    SLine i x => if minNestingLevel < i
                                    then go (lineLength - i) $ assert_smaller s x
                                    else True
                    SAnnPush _ x => go w x
                    SAnnPop x => go w x
layoutSmart (MkLayoutOptions Unbounded) = layoutUnbounded

||| Lays out the document without adding any indentation. This layouter is very fast.
export
layoutCompact : Doc ann -> SimpleDocStream ann
layoutCompact doc = scan 0 [doc]
  where
    scan : Int -> List (Doc ann) -> SimpleDocStream ann
    scan _ [] = SEmpty
    scan col (Empty :: ds) = scan col ds
    scan col ((Chara c) :: ds) = SChar c (scan (col + 1) ds)
    scan col ((Text l t) :: ds) = SText l t (scan (col + l) ds)
    scan col s@((FlatAlt x _) :: ds) = scan col $ assert_smaller s (x :: ds)
    scan col (Line :: ds) = SLine 0 (scan 0 ds)
    scan col s@((Cat x y) :: ds) = scan col $ assert_smaller s (x :: y :: ds)
    scan col s@((Nest _ x) :: ds) = scan col $ assert_smaller s (x :: ds)
    scan col s@((Union _ y) :: ds) = scan col $ assert_smaller s (y :: ds)
    scan col s@((Column f) :: ds) = scan col $ assert_smaller s (f col :: ds)
    scan col s@((WithPageWidth f) :: ds) = scan col $ assert_smaller s (f Unbounded :: ds)
    scan col s@((Nesting f) :: ds) = scan col $ assert_smaller s (f 0 :: ds)
    scan col s@((Annotated _ x) :: ds) = scan col $ assert_smaller s (x :: ds)


------------------------------------------------------------------------
-- Turn the document into a string
------------------------------------------------------------------------

export
renderShow : SimpleDocStream ann -> (String -> String)
renderShow SEmpty = id
renderShow (SChar c x) = (strCons c) . renderShow x
renderShow (SText _ t x) = (t ++) . renderShow x
renderShow (SLine i x) = ((strCons '\n' $ textSpaces i) ++) . renderShow x
renderShow (SAnnPush _ x) = renderShow x
renderShow (SAnnPop x) = renderShow x

export
Show (Doc ann) where
  show doc = renderShow (layoutPretty defaultLayoutOptions doc) ""

------------------------------------------------------------------------
-- Turn the document into a string, and a list of annotation spans
------------------------------------------------------------------------

export
displaySpans : SimpleDocStream a -> (String, List (Span a))
displaySpans p =
  let (bits, anns) = go Z [<] [<] [] p in
  (concat bits, anns)

  where

    go : (index : Nat) ->
         (doc   : SnocList String) ->
         (spans : SnocList (Span a)) ->
         (ann : List (Nat, a)) -> -- starting index, < current
         SimpleDocStream a ->
         (List String, List (Span a))
    go index doc spans ann SEmpty = (doc <>> [], spans <>> [])
    go index doc spans ann (SChar c rest)
      = go (S index) (doc :< cast c) spans ann rest
    go index doc spans ann (SText len text rest)
      = go (integerToNat (cast len) + index) (doc :< text) spans ann rest
    go index doc spans ann (SLine i rest)
      = let text = strCons '\n' (textSpaces i) in
        go (S (integerToNat $ cast i) + index) (doc :< text) spans ann rest
    go index doc spans ann (SAnnPush a rest)
      = go index doc spans ((index, a) :: ann) rest
    go index doc spans ((start, a) :: ann) (SAnnPop rest)
      = let span = MkSpan start (minus index start) a in
        go index doc (spans :< span) ann rest
    go index doc spans [] (SAnnPop rest)
      = go index doc spans [] rest
