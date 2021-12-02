module Idris.Pretty

import Core.Metadata
import Data.List
import Data.SnocList
import Data.Maybe
import Data.String
import Libraries.Control.ANSI.SGR

import Parser.Lexer.Source

import public Idris.Pretty.Render

import public Libraries.Text.PrettyPrint.Prettyprinter
import public Libraries.Text.PrettyPrint.Prettyprinter.Util

import Idris.REPL.Opts
import Idris.Syntax

%default covering

public export
data IdrisSyntax
  = Hole
  | TCon (Maybe Name) -- these may be primitive types
  | DCon (Maybe Name) -- these may be primitive constructors
  | Fun  Name
  | Bound
  | Keyword
  | Pragma

export
syntaxToDecoration : IdrisSyntax -> Maybe Decoration
syntaxToDecoration Hole     = Nothing
syntaxToDecoration (TCon{}) = pure Typ
syntaxToDecoration (DCon{}) = pure Data
syntaxToDecoration (Fun{})  = pure Function
syntaxToDecoration Bound    = pure Bound
syntaxToDecoration Keyword  = pure Keyword
syntaxToDecoration Pragma   = Nothing

export
kindAnn : KindedName -> Maybe IdrisSyntax
kindAnn (MkKindedName mcat fn nm) = do
    cat <- mcat
    pure $ case cat of
      Bound     => Bound
      Func      => Fun fn
      DataCon{} => DCon (Just fn)
      TyCon{}   => TCon (Just fn)

export
showCategory : (IdrisSyntax -> ann) -> GlobalDef -> Doc ann -> Doc ann
showCategory embed def = annotateM (embed <$> kindAnn (gDefKindedName def))

public export
data IdrisAnn
  = Warning
  | Error
  | ErrorDesc
  | FileCtxt
  | Code
  | Meta
  | Syntax IdrisSyntax
  | UserDocString

export
annToDecoration : IdrisAnn -> Maybe Decoration
annToDecoration (Syntax syn) = syntaxToDecoration syn
annToDecoration _ = Nothing

export
syntaxAnn : IdrisSyntax -> AnsiStyle
syntaxAnn Hole = color BrightGreen
syntaxAnn (TCon{}) = color BrightBlue
syntaxAnn (DCon{}) = color BrightRed
syntaxAnn (Fun{})  = color BrightGreen
syntaxAnn Bound    = italic
syntaxAnn Keyword  = color BrightWhite
syntaxAnn Pragma   = color BrightMagenta

export
colorAnn : IdrisAnn -> AnsiStyle
colorAnn Warning = color Yellow <+> bold
colorAnn Error = color BrightRed <+> bold
colorAnn ErrorDesc = bold
colorAnn FileCtxt = color BrightBlue
colorAnn Code = color Magenta
colorAnn Meta = color Green
colorAnn (Syntax syn) = syntaxAnn syn
colorAnn UserDocString = []

export
warning : Doc IdrisAnn -> Doc IdrisAnn
warning = annotate Warning

export
error : Doc IdrisAnn -> Doc IdrisAnn
error = annotate Error

export
errorDesc : Doc IdrisAnn -> Doc IdrisAnn
errorDesc = annotate ErrorDesc

export
fileCtxt : Doc IdrisAnn -> Doc IdrisAnn
fileCtxt = annotate FileCtxt

export
keyword : Doc IdrisSyntax -> Doc IdrisSyntax
keyword = annotate Keyword

export
meta : Doc IdrisAnn -> Doc IdrisAnn
meta = annotate Meta

export
hole : Doc IdrisSyntax -> Doc IdrisSyntax
hole = annotate Hole

export
code : Doc IdrisAnn -> Doc IdrisAnn
code = annotate Code

let_ : Doc IdrisSyntax
let_ = keyword (pretty "let")

in_ : Doc IdrisSyntax
in_ = keyword (pretty "in")

case_ : Doc IdrisSyntax
case_ = keyword (pretty "case")

of_ : Doc IdrisSyntax
of_ = keyword (pretty "of")

do_ : Doc IdrisSyntax
do_ = keyword (pretty "do")

with_ : Doc IdrisSyntax
with_ = keyword (pretty "with")

record_ : Doc IdrisSyntax
record_ = keyword (pretty "record")

impossible_ : Doc IdrisSyntax
impossible_ = keyword (pretty "impossible")

auto_ : Doc IdrisSyntax
auto_ = keyword (pretty "auto")

default_ : Doc IdrisSyntax
default_ = keyword (pretty "default")

rewrite_ : Doc IdrisSyntax
rewrite_ = keyword (pretty "rewrite")

export
pragma : Doc IdrisSyntax -> Doc IdrisSyntax
pragma = annotate Pragma

export
prettyRig : RigCount -> Doc ann
prettyRig = elimSemi (pretty '0' <+> space)
                     (pretty '1' <+> space)
                     (const emptyDoc)

mutual
  prettyAlt : PClause' KindedName -> Doc IdrisSyntax
  prettyAlt (MkPatClause _ lhs rhs _) =
    space <+> pipe <++> prettyTerm lhs <++> pretty "=>" <++> prettyTerm rhs <+> semi
  prettyAlt (MkWithClause _ lhs wval prf flags cs) =
    space <+> pipe <++> angles (angles (reflow "with alts not possible")) <+> semi
  prettyAlt (MkImpossible _ lhs) =
    space <+> pipe <++> prettyTerm lhs <++> impossible_ <+> semi

  prettyCase : PClause' KindedName -> Doc IdrisSyntax
  prettyCase (MkPatClause _ lhs rhs _) =
    prettyTerm lhs <++> pretty "=>" <++> prettyTerm rhs
  prettyCase (MkWithClause _ lhs rhs prf flags _) =
    space <+> pipe <++> angles (angles (reflow "with alts not possible"))
  prettyCase (MkImpossible _ lhs) =
    prettyTerm lhs <++> impossible_

  prettyString : PStr' KindedName -> Doc IdrisSyntax
  prettyString (StrLiteral _ str) = pretty str
  prettyString (StrInterp _ tm) = prettyTerm tm

  prettyDo : PDo' KindedName -> Doc IdrisSyntax
  prettyDo (DoExp _ tm) = prettyTerm tm
  prettyDo (DoBind _ _ n tm) = pretty n <++> pretty "<-" <++> prettyTerm tm
  prettyDo (DoBindPat _ l tm alts) =
    prettyTerm l <++> pretty "<-" <++> prettyTerm tm <+> hang 4 (fillSep $ prettyAlt <$> alts)
  prettyDo (DoLet _ _ l rig _ tm) =
    let_ <++> prettyRig rig <+> pretty l <++> equals <++> prettyTerm tm
  prettyDo (DoLetPat _ l _ tm alts) =
    let_ <++> prettyTerm l <++> equals <++> prettyTerm tm <+> hang 4 (fillSep $ prettyAlt <$> alts)
  prettyDo (DoLetLocal _ ds) =
    let_ <++> braces (angles (angles (pretty "definitions")))
  prettyDo (DoRewrite _ rule) = rewrite_ <+> prettyTerm rule

  prettyUpdate : PFieldUpdate' KindedName -> Doc IdrisSyntax
  prettyUpdate (PSetField path v) =
    concatWith (surround dot) (pretty <$> path) <++> equals <++> prettyTerm v
  prettyUpdate (PSetFieldApp path v) =
    concatWith (surround dot) (pretty <$> path) <++> pretty '$' <+> equals <++> prettyTerm v

  prettyBinder : Name -> Doc IdrisSyntax
  prettyBinder = annotate Bound . pretty

  export
  prettyTerm : IPTerm -> Doc IdrisSyntax
  prettyTerm = go Open
    where
      startPrec : Prec
      startPrec = Open
      appPrec : Prec
      appPrec = App
      leftAppPrec : Prec
      leftAppPrec = Open
      prettyOp : OpStr' KindedName -> Doc IdrisSyntax
      prettyOp op@(MkKindedName _ _ nm) = if isOpName nm
        then annotateM (kindAnn op) $ pretty nm
        else Chara '`' <+> annotateM (kindAnn op) (pretty nm) <+> Chara '`'

      go : Prec -> IPTerm -> Doc IdrisSyntax
      go d (PRef _ nm) = annotateM (kindAnn nm) $ pretty nm.rawName
      go d (PPi _ rig Explicit Nothing arg ret) =
        parenthesise (d > startPrec) $ group $
          branchVal
            (go startPrec arg <++> "->" <++> go startPrec ret)
            (parens (prettyRig rig <+> "_" <++> colon <++> go startPrec arg)
                    <++> "->" <+> softline <+> go startPrec ret)
            rig
      go d (PPi _ rig Explicit (Just n) arg ret) =
        parenthesise (d > startPrec) $ group $
          parens (prettyRig rig <+> prettyBinder n
                 <++> colon <++> go startPrec arg)
                  <++> "->" <+> softline <+> go startPrec ret
      go d (PPi _ rig Implicit Nothing arg ret) =
        parenthesise (d > startPrec) $ group $
          braces (prettyRig rig <+> pretty '_'
                 <++> colon <++> go startPrec arg)
                 <++> "->" <+> softline <+> go startPrec ret
      go d (PPi _ rig Implicit (Just n) arg ret) =
        parenthesise (d > startPrec) $ group $
          braces (prettyRig rig <+> prettyBinder n
                 <++> colon <++> go startPrec arg)
                 <++> "->" <+> softline <+> go startPrec ret
      go d (PPi _ rig AutoImplicit Nothing arg ret) =
        parenthesise (d > startPrec) $ group $
          branchVal
            (go startPrec arg <++> "=>" <+> softline <+> go startPrec ret)
            (braces (auto_ <++> prettyRig rig <+> "_"
                    <++> colon <++> go startPrec arg)
                    <++> "->" <+> softline <+> go startPrec ret)
            rig
      go d (PPi _ rig AutoImplicit (Just n) arg ret) =
        parenthesise (d > startPrec) $ group $
          braces (auto_ <++> prettyRig rig <+> prettyBinder n
                 <++> colon <++> go startPrec arg)
                 <++> "->" <+> softline <+> go startPrec ret
      go d (PPi _ rig (DefImplicit t) Nothing arg ret) =
        parenthesise (d > startPrec) $ group $
          braces (default_ <++> go appPrec t <++> prettyRig rig <+> "_"
                 <++> colon <++> go startPrec arg)
                 <++> "->" <+> softline <+> go startPrec ret
      go d (PPi _ rig (DefImplicit t) (Just n) arg ret) =
        parenthesise (d > startPrec) $ group $
          braces (default_ <++> go appPrec t
                 <++> prettyRig rig <+> prettyBinder n
                 <++> colon <++> go startPrec arg)
                 <++> "->" <+> softline <+> go startPrec ret
      go d (PLam _ rig _ n ty sc) =
          let (ns, sc) = getLamNames [(rig, n, ty)] sc in
              parenthesise (d > startPrec) $ group $
                backslash <+> prettyBindings ns <++> "=>" <+> softline <+> go startPrec sc
        where
          getLamNames : List (RigCount, IPTerm, IPTerm) ->
                        IPTerm ->
                        (List (RigCount, IPTerm, IPTerm), IPTerm)
          getLamNames acc (PLam _ rig _ n ty sc) = getLamNames ((rig, n, ty) :: acc) sc
          getLamNames acc sc = (reverse acc, sc)

          prettyBindings : List (RigCount, IPTerm, IPTerm) -> Doc IdrisSyntax
          prettyBindings [] = neutral
          prettyBindings [(rig, n, (PImplicit _))] = prettyRig rig <+> go startPrec n
          prettyBindings [(rig, n, ty)] = prettyRig rig <+> go startPrec n <++> colon <++> go startPrec ty
          prettyBindings ((rig, n, (PImplicit _)) :: ns) = prettyRig rig <+> go startPrec n <+> comma <+> line <+> prettyBindings ns
          prettyBindings ((rig, n, ty) :: ns) = prettyRig rig <+> go startPrec n <++> colon <++> go startPrec ty <+> comma <+> line <+> prettyBindings ns
      go d (PLet _ rig n (PImplicit _) val sc alts) =
          -- Hide uninformative lets
          -- (Those that look like 'let x = x in ...')
          -- Makes printing the types of names bound in where clauses a lot
          -- more readable
          fromMaybe fullLet $ do
            nName   <- getPRefName n
            valName <- getPRefName val
            guard (show nName == show valName)
            pure continuation

         -- Hide lets that bind to underscore
         -- That is, 'let _ = x in ...'
         -- Those end up polluting the types of let bound variables in some
         -- occasions
          <|> do
            nName <- getPRefName n
            guard (isUnderscoreName nName)
            pure continuation

        where

          continuation : Doc IdrisSyntax
          continuation = go startPrec sc

          fullLet : Doc IdrisSyntax
          fullLet = parenthesise (d > startPrec) $ group $ align $
            let_ <++> (group $ align $ hang 2 $ prettyRig rig <+> go startPrec n <++> equals <+> line <+> go startPrec val) <+> line
              <+> in_ <++> (group $ align $ hang 2 $ continuation)

          getPRefName : IPTerm -> Maybe Name
          getPRefName (PRef _ n) = Just (rawName n)
          getPRefName _ = Nothing

      go d (PLet _ rig n ty val sc alts) =
        parenthesise (d > startPrec) $ group $ align $
          let_ <++> (group $ align $ hang 2 $ prettyRig rig <+> go startPrec n <++> colon <++> go startPrec ty <++> equals <+> line <+> go startPrec val) <+> hardline
            <+> hang 4 (fillSep (prettyAlt <$> alts)) <+> line <+> in_ <++> (group $ align $ hang 2 $ go startPrec sc)
      go d (PCase _ tm cs) =
        parenthesise (d > startPrec) $ align $ case_ <++> go startPrec tm <++> of_ <+> line <+>
          braces (vsep $ punctuate semi (prettyCase <$> cs))
      go d (PLocal _ ds sc) =
        parenthesise (d > startPrec) $ group $ align $
          let_ <++> braces (angles (angles "definitions")) <+> line <+> in_ <++> go startPrec sc
      go d (PUpdate _ fs) =
        parenthesise (d > startPrec) $ group $ record_ <++> braces (vsep $ punctuate comma (prettyUpdate <$> fs))
      go d (PApp _ f a) =
        let catchall : Lazy (Doc IdrisSyntax)
               := go leftAppPrec f <++> go appPrec a

        in parenthesise (d >= appPrec) $ group $ case f of
          (PRef _ n) =>
            if isJust (isRF $ rawName n)
            then go leftAppPrec a <++> go appPrec f
            else catchall
          _ => catchall
      go d (PWithApp _ f a) = go d f <++> pipe <++> go d a
      go d (PDelayed _ LInf ty) = parenthesise (d > startPrec) $ "Inf" <++> go appPrec ty
      go d (PDelayed _ _ ty) = parenthesise (d > startPrec) $ "Lazy" <++> go appPrec ty
      go d (PDelay _ tm) = parenthesise (d > startPrec) $ "Delay" <++> go appPrec tm
      go d (PForce _ tm) = parenthesise (d > startPrec) $ "Force" <++> go appPrec tm
      go d (PAutoApp _ f a) =
        parenthesise (d > startPrec) $ group $ go leftAppPrec f <++> "@" <+> braces (go startPrec a)
      go d (PNamedApp _ f n (PRef _ a)) =
        parenthesise (d > startPrec) $ group $
          if n == rawName a
             then go leftAppPrec f <++> braces (pretty n)
             else go leftAppPrec f <++> braces (pretty n <++> equals <++> pretty a.rawName)
      go d (PNamedApp _ f n a) =
        parenthesise (d > startPrec) $ group $ go leftAppPrec f <++> braces (pretty n <++> equals <++> go d a)
      go d (PSearch _ _) = pragma "%search"
      go d (PQuote _ tm) = parenthesise (d > startPrec) $ "`" <+> parens (go startPrec tm)
      go d (PQuoteName _ n) = parenthesise (d > startPrec) $ "`" <+> braces (braces (pretty n))
      go d (PQuoteDecl _ tm) = parenthesise (d > startPrec) $ "`" <+> brackets (angles (angles (pretty "declaration")))
      go d (PUnquote _ tm) = parenthesise (d > startPrec) $ "~" <+> parens (go startPrec tm)
      go d (PRunElab _ tm) = parenthesise (d > startPrec) $ pragma "%runElab" <++> go startPrec tm
      go d (PPrimVal _ c) =
        let decor = if isPrimType c then TCon Nothing else DCon Nothing in
        annotate decor $ pretty c
      go d (PHole _ _ n) = hole (pretty (strCons '?' n))
      go d (PType _) = annotate (TCon Nothing) "Type"
      go d (PAs _ _ n p) = pretty n <+> "@" <+> go d p
      go d (PDotted _ p) = dot <+> go d p
      go d (PImplicit _) = "_"
      go d (PInfer _) = annotate Hole $ "?"
      go d (POp _ _ op x y) = parenthesise (d >= App) $ group $ go startPrec x <++> prettyOp op <++> go startPrec y
      go d (PPrefixOp _ _ op x) = parenthesise (d > startPrec) $ prettyOp op <+> go startPrec x
      go d (PSectionL _ _ op x) = parens (prettyOp op <++> go startPrec x)
      go d (PSectionR _ _ x op) = parens (go startPrec x <++> prettyOp op)
      go d (PEq fc l r) = parenthesise (d > startPrec) $ go Equal l <++> equals <++> go Equal r
      go d (PBracketed _ tm) = parens (go startPrec tm)
      go d (PString _ xs) = parenthesise (d > startPrec) $ hsep $ punctuate "++" (prettyString <$> xs)
      go d (PMultiline _ indent xs) = "multiline" <++> (parenthesise (d > startPrec) $ hsep $ punctuate "++" (prettyString <$> concat xs))
      go d (PDoBlock _ ns ds) = parenthesise (d > startPrec) $ group $ align $ hang 2 $ do_ <++> (vsep $ punctuate semi (prettyDo <$> ds))
      go d (PBang _ tm) = "!" <+> go d tm
      go d (PIdiom _ tm) = enclose (pretty "[|") (pretty "|]") (go startPrec tm)
      go d (PList _ _ xs) = brackets (group $ align $ vsep $ punctuate comma (go startPrec . snd <$> xs))
      go d (PSnocList _ _ xs)
        = brackets {ldelim = "[<"}
        $ group $ align $ vsep $ punctuate comma
        $ go startPrec . snd <$> (xs <>> [])
      go d (PPair _ l r) = group $ parens (go startPrec l <+> comma <+> line <+> go startPrec r)
      go d (PDPair _ _ l (PImplicit _) r) = group $ parens (go startPrec l <++> pretty "**" <+> line <+> go startPrec r)
      go d (PDPair _ _ l ty r) = group $ parens (go startPrec l <++> colon <++> go startPrec ty <++> pretty "**" <+> line <+> go startPrec r)
      go d (PUnit _) = "()"
      go d (PIfThenElse _ x t e) =
        parenthesise (d > startPrec) $ group $ align $ hang 2 $ vsep
          [keyword "if" <++> go startPrec x, keyword "then" <++> go startPrec t, keyword "else" <++> go startPrec e]
      go d (PComprehension _ ret es) =
          group $ brackets (go startPrec (dePure ret) <++> pipe <++> vsep (punctuate comma (prettyDo . deGuard <$> es)))
        where
          dePure : IPTerm -> IPTerm
          dePure tm@(PApp _ (PRef _ n) arg)
            = if dropNS (rawName n) == UN (Basic "pure") then arg else tm
          dePure tm = tm

          deGuard : PDo' KindedName -> PDo' KindedName
          deGuard tm@(DoExp fc (PApp _ (PRef _ n) arg))
            = if dropNS (rawName n) == UN (Basic "guard") then DoExp fc arg else tm
          deGuard tm = tm
      go d (PRewrite _ rule tm) =
        parenthesise (d > startPrec) $ group $ rewrite_ <++> go startPrec rule <+> line <+> in_ <++> go startPrec tm
      go d (PRange _ start Nothing end) =
        brackets (go startPrec start <++> pretty ".." <++> go startPrec end)
      go d (PRange _ start (Just next) end) =
        brackets (go startPrec start <+> comma <++> go startPrec next <++> pretty ".." <++> go startPrec end)
      go d (PRangeStream _ start Nothing) = brackets (go startPrec start <++> pretty "..")
      go d (PRangeStream _ start (Just next)) =
        brackets (go startPrec start <+> comma <++> go startPrec next <++> pretty "..")
      go d (PUnifyLog _ lvl tm) = go d tm
      go d (PPostfixApp fc rec fields) =
        parenthesise (d > startPrec) $ go startPrec rec <++> dot <+> concatWith (surround dot) (map pretty fields)
      go d (PPostfixAppPartial fc fields) =
        parens (dot <+> concatWith (surround dot) (map pretty fields))
      go d (PWithUnambigNames fc ns rhs) = parenthesise (d > startPrec) $ group $ with_ <++> pretty ns <+> line <+> go startPrec rhs

export
render : {auto o : Ref ROpts REPLOpts} -> Doc IdrisAnn -> Core String
render = render colorAnn

export
renderWithDecorations :
  {auto c : Ref Ctxt Defs} ->
  {auto o : Ref ROpts REPLOpts} ->
  (ann -> Maybe ann') ->
  Doc ann ->
  Core (String, List (Span ann'))
renderWithDecorations f doc =
  do (str, mspans) <- Render.renderWithSpans doc
     let spans = mapMaybe (traverse f) mspans
     pure (str, spans)
