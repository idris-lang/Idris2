module Idris.Pretty

import Control.ANSI.SGR -- FIXME: tmp
import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter.Util

import Idris.REPLOpts
import Idris.Syntax

%default covering

public export
data IdrisAnn
  = Warning
  | Error
  | ErrorDesc
  | FileCtxt
  | Code
  | Meta
  | Keyword
  | Pragma

export
colorAnn : IdrisAnn -> AnsiStyle
colorAnn Warning = color Yellow <+> bold
colorAnn Error = color BrightRed <+> bold
colorAnn ErrorDesc = bold
colorAnn FileCtxt = color BrightBlue
colorAnn Code = color Magenta
colorAnn Keyword = color Red
colorAnn Pragma = color BrightMagenta
colorAnn Meta = color Green

export
errorDesc : Doc IdrisAnn -> Doc IdrisAnn
errorDesc = annotate ErrorDesc

export
keyword : Doc IdrisAnn -> Doc IdrisAnn
keyword = annotate Keyword

export
meta : Doc IdrisAnn -> Doc IdrisAnn
meta = annotate Meta

export
code : Doc IdrisAnn -> Doc IdrisAnn
code = annotate Code

ite : Doc IdrisAnn -> Doc IdrisAnn -> Doc IdrisAnn -> Doc IdrisAnn
ite x t e = keyword (pretty "if") <++> x <++> align (fillSep [keyword (pretty "then") <++> t, keyword (pretty "else") <++> e])

let_ : Doc IdrisAnn
let_ = keyword (pretty "let")

in_ : Doc IdrisAnn
in_ = keyword (pretty "in")

case_ : Doc IdrisAnn
case_ = keyword (pretty "case")

of_ : Doc IdrisAnn
of_ = keyword (pretty "of")

do_ : Doc IdrisAnn
do_ = keyword (pretty "do")

with_ : Doc IdrisAnn
with_ = keyword (pretty "with")

record_ : Doc IdrisAnn
record_ = keyword (pretty "record")

impossible_ : Doc IdrisAnn
impossible_ = keyword (pretty "impossible")

auto_ : Doc IdrisAnn
auto_ = keyword (pretty "auto")

default_ : Doc IdrisAnn
default_ = keyword (pretty "default")

rewrite_ : Doc IdrisAnn
rewrite_ = keyword (pretty "rewrite")

export
pragma : Doc IdrisAnn -> Doc IdrisAnn
pragma = annotate Pragma

prettyParens : (1 _ : Bool) -> Doc ann -> Doc ann
prettyParens False s = s
prettyParens True s = parens s

prettyCon : Prec -> Doc ann -> Doc ann -> Doc ann
prettyCon d conName conArgs = prettyParens (d >= App) (conName <++> conArgs)

prettyRig : RigCount -> Doc ann
prettyRig = elimSemi (pretty '0' <+> space)
                     (pretty '1' <+> space)
                     (const emptyDoc)

mutual
  prettyAlt : PClause -> Doc IdrisAnn
  prettyAlt (MkPatClause _ lhs rhs _) =
    space <+> pipe <++> prettyTerm lhs <++> pretty "=>" <++> prettyTerm rhs <+> semi
  prettyAlt (MkWithClause _ lhs wval flags cs) =
    space <+> pipe <++> angles (angles (reflow "with alts not possible")) <+> semi
  prettyAlt (MkImpossible _ lhs) =
    space <+> pipe <++> prettyTerm lhs <++> impossible_ <+> semi

  prettyCase : PClause -> Doc IdrisAnn
  prettyCase (MkPatClause _ lhs rhs _) =
    prettyTerm lhs <++> pretty "=>" <++> prettyTerm rhs
  prettyCase (MkWithClause _ lhs rhs flags _) =
    space <+> pipe <++> angles (angles (reflow "with alts not possible"))
  prettyCase (MkImpossible _ lhs) =
    prettyTerm lhs <++> impossible_

  prettyDo : PDo -> Doc IdrisAnn
  prettyDo (DoExp _ tm) = prettyTerm tm
  prettyDo (DoBind _ n tm) = pretty n <++> pretty "<-" <++> prettyTerm tm
  prettyDo (DoBindPat _ l tm alts) =
    prettyTerm l <++> pretty "<-" <++> prettyTerm tm <+> hang 4 (fillSep $ prettyAlt <$> alts)
  prettyDo (DoLet _ l rig _ tm) =
    let_ <++> prettyRig rig <+> pretty l <++> equals <++> prettyTerm tm
  prettyDo (DoLetPat _ l _ tm alts) =
    let_ <++> prettyTerm l <++> equals <++> prettyTerm tm <+> hang 4 (fillSep $ prettyAlt <$> alts)
  prettyDo (DoLetLocal _ ds) =
    let_ <++> braces (angles (angles (pretty "definitions")))
  prettyDo (DoRewrite _ rule) = rewrite_ <+> prettyTerm rule

  prettyUpdate : PFieldUpdate -> Doc IdrisAnn
  prettyUpdate (PSetField path v) =
    concatWith (surround dot) (pretty <$> path) <++> equals <++> prettyTerm v
  prettyUpdate (PSetFieldApp path v) =
    concatWith (surround dot) (pretty <$> path) <++> pretty '$' <+> equals <++> prettyTerm v

  export
  prettyTerm : PTerm -> Doc IdrisAnn
  prettyTerm = go Open
    where
      go : Prec -> PTerm -> Doc IdrisAnn
      go d (PRef _ n) = pretty n
      go d (PPi _ rig Explicit Nothing arg ret) =
        go d arg <++> pretty "->" <++> go d ret
      go d (PPi _ rig Explicit (Just n) arg ret) =
        parens (prettyRig rig <+> pretty n <++> colon <++> go d arg) <++> pretty "->" <++> go d ret
      go d (PPi _ rig Implicit Nothing arg ret) =
        braces (prettyRig rig <+> pretty '_' <++> colon <++> go d arg) <++> pretty "->" <++> go d ret
      go d (PPi _ rig Implicit (Just n) arg ret) =
        braces (prettyRig rig <+> pretty n <++> colon <++> go d arg) <++> pretty "->" <++> go d ret
      go d (PPi _ rig AutoImplicit Nothing arg ret) =
        go d arg <++> pretty "=>" <++> go d ret
      go d (PPi _ rig AutoImplicit (Just n) arg ret) =
        braces (auto_ <++> prettyRig rig <+> pretty n <+> colon <+> go d arg) <++> pretty "->" <++> go d ret
      go d (PPi _ rig (DefImplicit t) Nothing arg ret) =
        braces (default_ <++> go App t <++> prettyRig rig <+> pretty '_' <++> colon <++> go d arg) <++> pretty "->" <++> go d ret
      go d (PPi _ rig (DefImplicit t) (Just n) arg ret) =
        braces (default_ <++> go App t <++> prettyRig rig <+> pretty n <++> colon <++> go d arg) <++> pretty "->" <++> go d ret
      go d (PLam _ rig _ n (PImplicit _) sc) =
        backslash <+> prettyRig rig <+> go d n <++> pretty "=>" <++> go d sc
      go d (PLam _ rig _ n ty sc) =
        backslash <+> prettyRig rig <+> go d n <++> colon <++> go d ty <++> pretty "=>" <++> go d sc
      go d (PLet _ rig n (PImplicit _) val sc alts) =
        let_ <++> prettyRig rig <+> go d n <++> equals <++> go d val <++> in_ <++> go d sc
      go d (PLet _ rig n ty val sc alts) =
        let_ <++> prettyRig rig <+> go d n <++> colon <++> go d ty <++> equals <++> go d val <+> hang 4 (fillSep (prettyAlt <$> alts)) <++> in_ <++> go d sc
      go d (PCase _ tm cs) =
        case_ <+> go d tm <++> of_ <++> braces (concatWith (surround semi) (prettyCase <$> cs))
      go d (PLocal _ ds sc) =
        let_ <++> braces (angles (angles (pretty "definitions"))) <++> in_ <++> go d sc
      go d (PUpdate _ fs) =
        record_ <++> braces (concatWith (surround (comma <+> space)) (prettyUpdate <$> fs))
      go d (PApp _ f a) = go App f <++> go App a
      go d (PWithApp _ f a) = go d f <++> pipe <++> go d a
      go d (PImplicitApp _ f Nothing a) = go d f <++> pretty '@' <+> braces (go d a)
      go d (PDelayed _ LInf ty) = prettyCon d (pretty "Inf") (go App ty)
      go d (PDelayed _ _ ty) = prettyCon d (pretty "Lazy") (go App ty)
      go d (PDelay _ tm) = prettyCon d (pretty "Delay") (go App tm)
      go d (PForce _ tm) = prettyCon d (pretty "Force") (go App tm)
      go d (PImplicitApp _ f (Just n) (PRef _ a)) =
        if n == a
           then go d f <++> braces (pretty n)
           else go d f <++> braces (pretty n <++> equals <++> pretty a)
      go d (PImplicitApp _ f (Just n) a) =
        go d f <++> braces (pretty n <++> equals <++> go d a)
      go d (PSearch _ _) = pragma (pretty "%search")
      go d (PQuote _ tm) = pretty '`' <+> parens (go d tm)
      go d (PQuoteName _ n) = pretty '`' <+> braces (braces (pretty n))
      go d (PQuoteDecl _ tm) = pretty '`' <+> brackets (angles (angles (pretty "declaration")))
      go d (PUnquote _ tm) = pretty '~' <+> parens (go d tm)
      go d (PRunElab _ tm) = pragma (pretty "%runElab") <++> go d tm
      go d (PPrimVal _ c) = pretty c
      go d (PHole _ _ n) = meta (pretty (strCons '?' n))
      go d (PType _) = pretty "Type"
      go d (PAs _ n p) = pretty n <+> pretty '@' <+> go d p
      go d (PDotted _ p) = dot <+> go d p
      go d (PImplicit _) = pretty '_'
      go d (PInfer _) = pretty '?'
      go d (POp _ op x y) = go d x <++> pretty op <++> go d y
      go d (PPrefixOp _ op x) = pretty op <+> go d x
      go d (PSectionL _ op x) = parens (pretty op <++> go d x)
      go d (PSectionR _ x op) = parens (go d x <++> pretty op)
      go d (PEq fc l r) = go d l <++> equals <++> go d r
      go d (PBracketed _ tm) = parens (go d tm)
      go d (PDoBlock _ ns ds) = do_ <++> concatWith (surround (space <+> semi <+> space)) (prettyDo <$> ds)
      go d (PBang _ tm) = pretty '!' <+> go d tm
      go d (PIdiom _ tm) = enclose (pretty "[|") (pretty "|]") (go d tm)
      go d (PList _ xs) = brackets (concatWith (surround (comma <+> space)) (go d <$> xs))
      go d (PPair _ l r) = parens (go d l <+> comma <++> go d r)
      go d (PDPair _ l (PImplicit _) r) = parens (go d l <++> pretty "**" <++> go d r)
      go d (PDPair _ l ty r) = parens (go d l <++> colon <++> go d ty <++> pretty "**" <++> go d r)
      go d (PUnit _) = pretty "()"
      go d (PIfThenElse _ x t e) = ite (go d x) (go d t) (go d e)
      go d (PComprehension _ ret es) =
         brackets (go d (dePure ret) <++> pipe <++> concatWith (surround (comma <+> space)) (prettyDo . deGuard <$> es))
        where
          dePure : PTerm -> PTerm
          dePure tm@(PApp _ (PRef _ n) arg) = if dropNS n == UN "pure" then arg else tm
          dePure tm = tm

          deGuard : PDo -> PDo
          deGuard tm@(DoExp fc (PApp _ (PRef _ n) arg)) = if dropNS n == UN "guard" then DoExp fc arg else tm
          deGuard tm = tm
      go d (PRewrite _ rule tm) = rewrite_ <++> go d rule <++> in_ <++> go d tm
      go d (PRange _ start Nothing end) =
        brackets (go d start <++> pretty ".." <++> go d end)
      go d (PRange _ start (Just next) end) =
        brackets (go d start <+> comma <++> go d next <++> pretty ".." <++> go d end)
      go d (PRangeStream _ start Nothing) = brackets (go d start <++> pretty "..")
      go d (PRangeStream _ start (Just next)) =
        brackets (go d start <+> comma <++> go d next <++> pretty "..")
      go d (PUnifyLog _ lvl tm) = go d tm
      go d (PPostfixProjs fc rec fields) =
        go d rec <++> dot <+> concatWith (surround dot) (go d <$> fields)
      go d (PPostfixProjsSection fc fields args) =
        parens (dot <+> concatWith (surround dot) (go d <$> fields) <+> fillSep (go App <$> args))
      go d (PWithUnambigNames fc ns rhs) = with_ <++> pretty ns <++> go d rhs

export
render : {auto o : Ref ROpts REPLOpts} -> Doc IdrisAnn -> Core String
render doc = do
  consoleWidth <- getConsoleWidth
  color <- getColor
  let opts = MkLayoutOptions $ if consoleWidth == 0
                                  then Unbounded
                                  else AvailablePerLine (cast consoleWidth) 1
  let layout = layoutPretty opts doc
  pure $ renderString $ if color then reAnnotateS colorAnn layout else unAnnotateS layout

export
renderWithoutColor : {auto o : Ref ROpts REPLOpts} -> Doc IdrisAnn -> Core String
renderWithoutColor doc = do
  consoleWidth <- getConsoleWidth
  let opts = MkLayoutOptions $ if consoleWidth == 0
                                  then Unbounded
                                  else AvailablePerLine (cast consoleWidth) 1
  let layout = layoutPretty opts doc
  pure $ renderString $ unAnnotateS layout
