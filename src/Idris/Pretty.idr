module Idris.Pretty

import Core.Metadata
import Data.List
import Data.SnocList
import Data.Maybe
import Data.String
import Libraries.Control.ANSI.SGR
import Libraries.Data.String.Extra

import Parser.Lexer.Source

import public Idris.Pretty.Annotations
import public Idris.Pretty.Render

import public Libraries.Text.PrettyPrint.Prettyprinter
import public Libraries.Text.PrettyPrint.Prettyprinter.Util

import Idris.REPL.Opts
import Idris.Syntax

%default covering

%hide Symbols.equals
%hide Symbols.semi

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
meta : Doc IdrisAnn -> Doc IdrisAnn
meta = annotate Meta

export
code : Doc IdrisAnn -> Doc IdrisAnn
code = annotate Code

mutual

  prettyAlt : PClause' KindedName -> Doc IdrisSyntax
  prettyAlt (MkPatClause _ lhs rhs _) =
      space <+> pipe <++> pretty lhs <++> fatArrow <++> pretty rhs <+> semi
  prettyAlt (MkWithClause _ lhs wps flags cs) =
      space <+> pipe <++> angles (angles (reflow "with alts not possible")) <+> semi
  prettyAlt (MkImpossible _ lhs) =
      space <+> pipe <++> pretty lhs <++> impossible_ <+> semi

  prettyPClause : PClause' KindedName -> Doc IdrisSyntax
  prettyPClause (MkPatClause _ lhs rhs _) =
      pretty lhs <++> fatArrow <++> pretty rhs
  prettyPClause (MkWithClause _ lhs wps flags _) =
      space <+> pipe <++> angles (angles (reflow "with alts not possible"))
  prettyPClause (MkImpossible _ lhs) =
      pretty lhs <++> impossible_

  prettyPStr : PStr' KindedName -> Doc IdrisSyntax
  prettyPStr (StrLiteral _ str) = pretty0 str
  prettyPStr (StrInterp _ tm) = pretty tm

  prettyPDo : PDo' KindedName -> Doc IdrisSyntax
  prettyPDo (DoExp _ tm) = pretty tm
  prettyPDo (DoBind _ _ n tm) = pretty0 n <++> keyword "<-" <++> pretty tm
  prettyPDo (DoBindPat _ l tm alts) =
      pretty l <++> keyword "<-" <++> pretty tm <+> hang 4 (fillSep $ prettyAlt <$> alts)
  prettyPDo (DoLet _ _ l rig _ tm) =
      let_ <++> prettyRig rig <+> pretty0 l <++> equals <++> pretty tm
  prettyPDo (DoLetPat _ l _ tm alts) =
      let_ <++> pretty l <++> equals <++> pretty tm <+> hang 4 (fillSep $ prettyAlt <$> alts)
  prettyPDo (DoLetLocal _ ds) =
      let_ <++> braces (angles (angles "definitions"))
  prettyPDo (DoRewrite _ rule) = rewrite_ <+> pretty rule

  export
  prettyFieldPath : List String -> Doc IdrisSyntax
  prettyFieldPath flds = concatWith (surround $ keyword "->") (pretty0 <$> flds)

  prettyPFieldUpdate : PFieldUpdate' KindedName -> Doc IdrisSyntax
  prettyPFieldUpdate (PSetField path v) =
      prettyFieldPath path <++> equals <++> pretty v
  prettyPFieldUpdate (PSetFieldApp path v) =
      prettyFieldPath path <++> keyword "$=" <++> pretty v

  prettyBinder : Name -> Doc IdrisSyntax
  prettyBinder = annotate Bound . pretty0

  startPrec : Prec
  startPrec = Open
  appPrec : Prec
  appPrec = App
  leftAppPrec : Prec
  leftAppPrec = Open

  prettyOp : KindedName -> Doc IdrisSyntax
  prettyOp op@(MkKindedName _ _ nm) = if isOpName nm
      then annotateM (kindAnn op) $ pretty0 nm
      else Chara '`' <+> annotateM (kindAnn op) (pretty0 nm) <+> Chara '`'

  export
  Pretty IdrisSyntax IPTerm where
    prettyPrec d (PRef _ nm) = annotateM (kindAnn nm) $ cast $ prettyOp False nm.rawName
    prettyPrec d (PPi _ rig Explicit Nothing arg ret) =
      parenthesise (d > startPrec) $ group $
        branchVal
          (pretty arg <++> arrow <++> pretty ret)
          (parens (prettyRig rig <+> "_" <++> colon <++> pretty arg)
                  <++> arrow <+> softline <+> pretty ret)
          rig
    prettyPrec d (PPi _ rig Explicit (Just n) arg ret) =
      parenthesise (d > startPrec) $ group $
        parens (prettyRig rig <+> prettyBinder n
             <++> colon <++> pretty arg)
             <++> arrow <+> softline <+> pretty ret
    prettyPrec d (PPi _ rig Implicit Nothing arg ret) =
      parenthesise (d > startPrec) $ group $
        braces (prettyRig rig <+> pretty0 Underscore
             <++> colon <++> pretty arg)
             <++> arrow <+> softline <+> pretty ret
    prettyPrec d (PPi _ rig Implicit (Just n) arg ret) =
      parenthesise (d > startPrec) $ group $
        braces (prettyRig rig <+> prettyBinder n
             <++> colon <++> pretty arg)
             <++> arrow <+> softline <+> pretty ret
    prettyPrec d (PPi _ rig AutoImplicit Nothing arg ret) =
      parenthesise (d > startPrec) $ group $
        branchVal
          (pretty arg <++> fatArrow <+> softline <+> pretty ret)
          (braces (auto_ <++> prettyRig rig <+> "_"
                <++> colon <++> pretty arg)
                <++> arrow <+> softline <+> pretty ret)
          rig
    prettyPrec d (PPi _ rig AutoImplicit (Just n) arg ret) =
      parenthesise (d > startPrec) $ group $
        braces (auto_ <++> prettyRig rig <+> prettyBinder n
             <++> colon <++> pretty arg)
             <++> arrow <+> softline <+> pretty ret
    prettyPrec d (PPi _ rig (DefImplicit t) Nothing arg ret) =
      parenthesise (d > startPrec) $ group $
        braces (default_ <++> prettyPrec appPrec t <++> prettyRig rig <+> "_"
             <++> colon <++> pretty arg)
             <++> arrow <+> softline <+> pretty ret
    prettyPrec d (PPi _ rig (DefImplicit t) (Just n) arg ret) =
      parenthesise (d > startPrec) $ group $
        braces (default_ <++> prettyPrec appPrec t
             <++> prettyRig rig <+> prettyBinder n
             <++> colon <++> pretty arg)
             <++> arrow <+> softline <+> pretty ret
    prettyPrec d (PLam _ rig _ n ty sc) =
      let (ns, sc) = getLamNames [(rig, n, ty)] sc in
          parenthesise (d > startPrec) $ group $
            backslash <+> prettyBindings ns <++> fatArrow <+> softline <+> pretty sc
      where
      getLamNames : List (RigCount, IPTerm, IPTerm) ->
                    IPTerm ->
                    (List (RigCount, IPTerm, IPTerm), IPTerm)
      getLamNames acc (PLam _ rig _ n ty sc) = getLamNames ((rig, n, ty) :: acc) sc
      getLamNames acc sc = (reverse acc, sc)

      prettyBindings : List (RigCount, IPTerm, IPTerm) -> Doc IdrisSyntax
      prettyBindings [] = neutral
      prettyBindings [(rig, n, (PImplicit _))] = prettyRig rig <+> pretty n
      prettyBindings [(rig, n, ty)] = prettyRig rig <+> pretty n <++> colon <++> pretty ty
      prettyBindings ((rig, n, (PImplicit _)) :: ns) = prettyRig rig <+> pretty n
                                              <+> comma <+> line <+> prettyBindings ns
      prettyBindings ((rig, n, ty) :: ns) = prettyRig rig <+> pretty n <++> colon <++> pretty ty
                                              <+> comma <+> line <+> prettyBindings ns
    prettyPrec d (PLet _ rig n (PImplicit _) val sc alts) =
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
      continuation = pretty sc

      fullLet : Doc IdrisSyntax
      fullLet = parenthesise (d > startPrec) $ group $ align $
        let_ <++> (group $ align $ hang 2 $ prettyRig rig <+> pretty n <++> equals <+> line <+> pretty val) <+> line
          <+> in_ <++> (group $ align $ hang 2 $ continuation)

      getPRefName : IPTerm -> Maybe Name
      getPRefName (PRef _ n) = Just (rawName n)
      getPRefName _ = Nothing

    prettyPrec d (PLet _ rig n ty val sc alts) =
      parenthesise (d > startPrec) $ group $ align $
        let_ <++> (group $ align $ hang 2 $
                      prettyRig rig <+> pretty n <++> colon <++> pretty ty
                      <++> equals <+> line <+> pretty val)
        <+> case alts of
             { [] => in_ <+> softline
             ; _ => hardline <+> indent 4 (vsep (prettyAlt <$> alts)) <+> hardline <+> in_
             }
        <+> group (align $ hang 2 $ pretty sc)
    prettyPrec d (PCase _ tm cs) =
      parenthesise (d > startPrec) $
        case_ <++> pretty tm <++> of_ <+> nest 2 (
        let punctuation = lcurly :: (semi <$ fromMaybe [] (tail' [1..length cs])) in
        line <+> (vsep $ zipWith (<++>) punctuation (prettyPClause <$> cs) ++ [rcurly]))
    prettyPrec d (PLocal _ ds sc) =
      parenthesise (d > startPrec) $ group $ align $
        let_ <++> braces (angles (angles "definitions")) <+> line <+> in_ <++> pretty sc
    prettyPrec d (PUpdate _ fs) =
      parenthesise (d > startPrec) $ group $
        record_ <++> braces (vsep $ punctuate comma (prettyPFieldUpdate <$> fs))
    prettyPrec d (PApp _ f a) =
      let catchall : Lazy (Doc IdrisSyntax)
           := prettyPrec leftAppPrec f <++> prettyPrec appPrec a

      in parenthesise (d >= appPrec) $ group $ case f of
        (PRef _ n) =>
          if isJust (isRF $ rawName n)
          then prettyPrec leftAppPrec a <++> prettyPrec appPrec f
          else catchall
        _ => catchall
    prettyPrec d (PWithApp _ f a) = prettyPrec d f <++> pipe <++> prettyPrec d a
    prettyPrec d (PDelayed _ LInf ty) = parenthesise (d > startPrec) $ "Inf" <++> prettyPrec appPrec ty
    prettyPrec d (PDelayed _ _ ty) = parenthesise (d > startPrec) $ "Lazy" <++> prettyPrec appPrec ty
    prettyPrec d (PDelay _ tm) = parenthesise (d > startPrec) $ "Delay" <++> prettyPrec appPrec tm
    prettyPrec d (PForce _ tm) = parenthesise (d > startPrec) $ "Force" <++> prettyPrec appPrec tm
    prettyPrec d (PAutoApp _ f a) =
    parenthesise (d > startPrec) $ group $ prettyPrec leftAppPrec f <++> "@" <+> braces (pretty a)
    prettyPrec d (PNamedApp _ f n (PRef _ a)) =
      parenthesise (d > startPrec) $ group $
        if n == rawName a
           then prettyPrec leftAppPrec f <++> braces (pretty0 n)
           else prettyPrec leftAppPrec f <++> braces (pretty0 n <++> equals <++> pretty0 a.rawName)
    prettyPrec d (PNamedApp _ f n a) =
      parenthesise (d > startPrec) $ group $
        prettyPrec leftAppPrec f <++> braces (pretty0 n <++> equals <++> prettyPrec d a)
    prettyPrec d (PSearch _ _) = pragma "%search"
    prettyPrec d (PQuote _ tm) = parenthesise (d > startPrec) $ "`" <+> parens (pretty tm)
    prettyPrec d (PQuoteName _ n) = parenthesise (d > startPrec) $ "`" <+> braces (pretty0 n)
    prettyPrec d (PQuoteDecl _ tm) =
      parenthesise (d > startPrec) $
         "`" <+> brackets (angles (angles "declaration"))
    prettyPrec d (PUnquote _ tm) = parenthesise (d > startPrec) $ "~" <+> parens (pretty tm)
    prettyPrec d (PRunElab _ tm) = parenthesise (d > startPrec) $ pragma "%runElab" <++> pretty tm
    prettyPrec d (PPrimVal _ c) = pretty c
    prettyPrec d (PHole _ _ n) = hole (pretty0 (strCons '?' n))
    prettyPrec d (PType _) = annotate (TCon Nothing) "Type"
    prettyPrec d (PAs _ _ n p) = pretty0 n <+> "@" <+> prettyPrec d p
    prettyPrec d (PDotted _ p) = dot <+> prettyPrec d p
    prettyPrec d (PImplicit _) = "_"
    prettyPrec d (PInfer _) = annotate Hole $ "?"
    prettyPrec d (POp _ _ op x y) =
      parenthesise (d >= App) $
        group $ pretty x
           <++> prettyOp op
           <++> pretty y
    prettyPrec d (PPrefixOp _ _ op x) = parenthesise (d > startPrec) $ prettyOp op <+> pretty x
    prettyPrec d (PSectionL _ _ op x) = parens (prettyOp op <++> pretty x)
    prettyPrec d (PSectionR _ _ x op) = parens (pretty x <++> prettyOp op)
    prettyPrec d (PEq fc l r) = parenthesise (d > startPrec) $ prettyPrec Equal l <++> equals <++> prettyPrec Equal r
    prettyPrec d (PBracketed _ tm) = parens (pretty tm)
    prettyPrec d (PString _ xs) = parenthesise (d > startPrec) $ hsep $ punctuate "++" (prettyPStr <$> xs)
    prettyPrec d (PMultiline _ indent xs) =
      "multiline" <++>
        (parenthesise (d > startPrec) $
           hsep $ punctuate "++" (prettyPStr <$> concat xs))
    prettyPrec d (PDoBlock _ ns ds) =
      parenthesise (d > startPrec) $ group $ align $ hang 2 $
        do_ <++> (vsep $ punctuate semi (prettyPDo <$> ds))
    prettyPrec d (PBang _ tm) = "!" <+> prettyPrec d tm
    prettyPrec d (PIdiom _ Nothing tm) = enclose (keyword "[|") (keyword "|]") (pretty tm)
    prettyPrec d (PIdiom _ (Just ns) tm) = enclose (pretty0 ns <+> keyword ".[|") (keyword "|]") (pretty tm)
    prettyPrec d (PList _ _ xs) = brackets (group $ align $ vsep $ punctuate comma (pretty . snd <$> xs))
    prettyPrec d (PSnocList _ _ xs)
      = brackets {ldelim = "[<"}
      $ group $ align $ vsep $ punctuate comma
      $ pretty . snd <$> (xs <>> [])
    prettyPrec d (PPair _ l r) = group $ parens (pretty l <+> comma <+> line <+> pretty r)
    prettyPrec d (PDPair _ _ l (PImplicit _) r) = group $ parens (pretty l <++> keyword "**" <+> line <+> pretty r)
    prettyPrec d (PDPair _ _ l ty r) =
      group $ parens (pretty l <++> colon <++> pretty ty <++> keyword "**" <+> line <+> pretty r)
    prettyPrec d (PUnit _) = "()"
    prettyPrec d (PIfThenElse _ x t e) =
      parenthesise (d > startPrec) $ group $ align $ hang 2 $ vsep
        [ keyword "if" <++> pretty x
        , keyword "then" <++> pretty t
        , keyword "else" <++> pretty e]
    prettyPrec d (PComprehension _ ret es) =
      group $ brackets (pretty (dePure ret) <++> pipe <++> vsep (punctuate comma (prettyPDo . deGuard <$> es)))
      where
      dePure : IPTerm -> IPTerm
      dePure tm@(PApp _ (PRef _ n) arg)
        = if dropNS (rawName n) == UN (Basic "pure") then arg else tm
      dePure tm = tm

      deGuard : PDo' KindedName -> PDo' KindedName
      deGuard tm@(DoExp fc (PApp _ (PRef _ n) arg))
        = if dropNS (rawName n) == UN (Basic "guard") then DoExp fc arg else tm
      deGuard tm = tm
    prettyPrec d (PRewrite _ rule tm) =
      parenthesise (d > startPrec) $ group $
        rewrite_ <++> pretty rule <+> line <+> in_ <++> pretty tm
    prettyPrec d (PRange _ start Nothing end) =
      brackets (pretty start <++> keyword ".." <++> pretty end)
    prettyPrec d (PRange _ start (Just next) end) =
      brackets (pretty start <+> comma <++> pretty next <++> keyword ".." <++> pretty end)
    prettyPrec d (PRangeStream _ start Nothing) = brackets (pretty start <++> keyword "..")
    prettyPrec d (PRangeStream _ start (Just next)) =
      brackets (pretty start <+> comma <++> pretty next <++> keyword "..")
    prettyPrec d (PUnifyLog _ lvl tm) = prettyPrec d tm
    prettyPrec d (PPostfixApp fc rec fields) =
      parenthesise (d > startPrec) $
        pretty rec <++> dot <+> concatWith (surround dot) (map (pretty0 . snd) fields)
    prettyPrec d (PPostfixAppPartial fc fields) =
      parens (dot <+> concatWith (surround dot) (map (pretty0 . snd) fields))
    prettyPrec d (PWithUnambigNames fc ns rhs) =
      parenthesise (d > startPrec) $ group $
        with_ <++> cast (prettyList $ map snd ns) <+> line <+> pretty rhs

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

export
prettyImport : Import -> Doc IdrisSyntax
prettyImport (MkImport loc reexport path nameAs)
  = keyword "import"
    <+> ifThenElse reexport (space <+> keyword "public") ""
    <++> pretty0 path
    <+> ifThenElse (miAsNamespace path /= nameAs) (space <+> keyword "as" <++> pretty0 nameAs) ""
