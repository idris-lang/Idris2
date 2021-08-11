module Idris.Pretty

import Core.Context.Log
import Core.Metadata
import Data.List
import Data.Maybe
import Data.String
import Libraries.Control.ANSI.SGR

import Parser.Lexer.Source

import public Idris.Pretty.Render

import public Libraries.Text.PrettyPrint.Prettyprinter
import public Libraries.Text.PrettyPrint.Prettyprinter.Util

import Algebra
import Idris.REPL.Opts
import Idris.Syntax

%default covering

public export
data IdrisSyntax
  = SynHole
  | SynDecor Decoration
  | SynPragma
  | SynRef Name

public export
data IdrisAnn
  = Warning
  | Error
  | ErrorDesc
  | FileCtxt
  | Code
  | Meta
  | Syntax IdrisSyntax

export
colorAnn : IdrisAnn -> AnsiStyle
colorAnn Warning = color Yellow <+> bold
colorAnn Error = color BrightRed <+> bold
colorAnn ErrorDesc = bold
colorAnn FileCtxt = color BrightBlue
colorAnn Code = color Magenta
colorAnn Meta = color Green
colorAnn (Syntax SynHole) = color BrightGreen
colorAnn (Syntax (SynDecor Keyword)) = color BrightWhite
colorAnn (Syntax (SynDecor Typ)) = color BrightBlue
colorAnn (Syntax (SynDecor Data)) = color BrightRed
colorAnn (Syntax (SynDecor Function)) = color BrightGreen
colorAnn (Syntax (SynDecor Bound)) = italic
colorAnn (Syntax SynPragma) = color BrightMagenta
colorAnn (Syntax (SynRef _)) = []

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
keyword = annotate (SynDecor Keyword)

export
meta : Doc IdrisAnn -> Doc IdrisAnn
meta = annotate Meta

export
hole : Doc IdrisSyntax -> Doc IdrisSyntax
hole = annotate SynHole

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
pragma = annotate SynPragma

export
prettyRig : RigCount -> Doc ann
prettyRig = elimSemi (pretty '0' <+> space)
                     (pretty '1' <+> space)
                     (const emptyDoc)

export
fullNamespace : {auto c : Ref Ctxt Defs} ->
                Core Bool
fullNamespace
    = do pp <- getPPrint
         pure (fullNamespace pp)

export
cleanName : {auto c : Ref Ctxt Defs} ->
            Name -> Core Name
cleanName nm = case nm of
      MN n _     => pure (UN n)
      PV n _     => pure n
      DN n _     => pure (UN n)
      NS ns n    => cleanName n
      Nested _ n => cleanName n
      RF n       => pure (RF n)
      _          => UN <$> prettyName nm

mutual
  prettyAlt : {auto c : Ref Ctxt Defs} ->
              PClause -> Core (Doc IdrisSyntax)
  prettyAlt (MkPatClause _ lhs rhs _) =
    pure $ space <+> pipe <++> !(prettyTerm lhs)
           <++> pretty "=>" <++> !(prettyTerm rhs) <+> semi
  prettyAlt (MkWithClause _ lhs wval prf flags cs) =
    pure $ space <+> pipe <++> angles (angles (reflow "with alts not possible")) <+> semi
  prettyAlt (MkImpossible _ lhs) =
    pure $ space <+> pipe <++> !(prettyTerm lhs) <++> impossible_ <+> semi

  prettyCase : {auto c : Ref Ctxt Defs} ->
               PClause -> Core (Doc IdrisSyntax)
  prettyCase (MkPatClause _ lhs rhs _) =
    pure $ !(prettyTerm lhs) <++> pretty "=>" <++> !(prettyTerm rhs)
  prettyCase (MkWithClause _ lhs rhs prf flags _) =
    pure $ space <+> pipe <++> angles (angles (reflow "with alts not possible"))
  prettyCase (MkImpossible _ lhs) =
    pure $ !(prettyTerm lhs) <++> impossible_

  prettyString : {auto c : Ref Ctxt Defs} ->
                 PStr -> Core (Doc IdrisSyntax)
  prettyString (StrLiteral _ str) = pure $ pretty str
  prettyString (StrInterp _ tm) = prettyTerm tm

  prettyDo : {auto c : Ref Ctxt Defs} ->
             PDo -> Core (Doc IdrisSyntax)
  prettyDo (DoExp _ tm) = prettyTerm tm
  prettyDo (DoBind _ _ n tm) =
    pure $ pretty n <++> pretty "<-" <++> !(prettyTerm tm)
  prettyDo (DoBindPat _ l tm alts) =
    pure $ !(prettyTerm l) <++> pretty "<-" <++> !(prettyTerm tm)
         <+> hang 4 (fillSep $ !(traverse prettyAlt alts))
  prettyDo (DoLet _ _ l rig _ tm) =
    pure $ let_ <++> prettyRig rig <+> pretty l
           <++> equals <++> !(prettyTerm tm)
  prettyDo (DoLetPat _ l _ tm alts) =
    pure $ let_ <++> !(prettyTerm l)
           <++> equals <++> !(prettyTerm tm)
            <+> hang 4 (fillSep !(traverse prettyAlt alts))
  prettyDo (DoLetLocal _ ds) =
    pure $ let_ <++> braces (angles (angles (pretty "definitions")))
  prettyDo (DoRewrite _ rule) = pure $ rewrite_ <+> !(prettyTerm rule)

  prettyUpdate : {auto c : Ref Ctxt Defs} ->
                 PFieldUpdate -> Core (Doc IdrisSyntax)
  prettyUpdate (PSetField path v) =
    pure $ concatWith (surround dot) (pretty <$> path)
           <++> equals <++> !(prettyTerm v)
  prettyUpdate (PSetFieldApp path v) =
    pure $ concatWith (surround dot) (pretty <$> path)
         <++> pretty '$' <+> equals <++> !(prettyTerm v)

  export
  prettyTerm : {auto c : Ref Ctxt Defs} ->
               PTerm -> Core (Doc IdrisSyntax)
  prettyTerm = go Open
    where
      startPrec : Prec
      startPrec = User 0
      appPrec : Prec
      appPrec = User 10
      leftAppPrec : Prec
      leftAppPrec = User 9
      prettyOp : OpStr -> Doc IdrisSyntax
      prettyOp op = if isOpName op
        then annotate (SynRef op) $ pretty op
        else Chara '`' <+> annotate (SynRef op) (pretty op) <+> Chara '`'

      go : Prec -> PTerm -> Core (Doc IdrisSyntax)
      go d (PRef _ n@(NS _ _))
        = do defs <- get Ctxt
             ns <- fullNamespace
             n' <- ifThenElse ns (pure n) (cleanName n)
             let dflt = annotate (SynRef n) $ pretty n'
             log "pretty.colour" 20 $ "Looking up " ++ show n
             [(_,_,def)] <- lookupDefName n (gamma defs)
               | [] => pure $ annotate (SynDecor Bound) dflt
               | _ => pure dflt
             log "pretty.colour" 20 $ "Got " ++ show def
             let Just decor = defDecoration def
               | Nothing => pure dflt
             pure $ annotate (SynDecor decor) dflt
      go d (PRef _ n) =
        pure $ annotate (SynDecor Bound) $ annotate (SynRef n) $ pretty n
      go d (PPi _ rig Explicit Nothing arg ret) = do
        parg <- go startPrec arg
        pret <- go startPrec ret
        pure $ parenthesise (d > startPrec) $ group $
          branchVal
            (parg <++> "->" <++> pret)
            (parens (prettyRig rig <+> "_" <++> colon <++> parg)
                     <++> "->" <+> line <+> pret)
            rig
      go d (PPi _ rig Explicit (Just n) arg ret) =
        pure $ parenthesise (d > startPrec) $ group $
          parens (prettyRig rig <+> pretty n <++> colon <++> !(go startPrec arg))
           <++> "->" <+> line <+> !(go startPrec ret)
      go d (PPi _ rig Implicit Nothing arg ret) =
        pure $ parenthesise (d > startPrec) $ group $
          braces (prettyRig rig <+> pretty '_' <++> colon <++> !(go startPrec arg))
            <++> "->" <+> line <+> !(go startPrec ret)
      go d (PPi _ rig Implicit (Just n) arg ret) =
        pure $ parenthesise (d > startPrec) $ group $
          braces (prettyRig rig <+> pretty n <++> colon <++> !(go startPrec arg))
            <++> "->" <+> line <+> !(go startPrec ret)
      go d (PPi _ rig AutoImplicit mnm arg ret) = do
        parg <- go startPrec arg
        pret <- go startPrec ret
        let prig = prettyRig rig
        pure $ parenthesise (d > startPrec) $ group $
        -- If the name is machine generated then act as if it were not given
          case (mnm >>= \nm => guard (isSourceName nm)) of
            Nothing => branchVal
              (parg <++> "=>" <+> line <+> pret)
              (braces (auto_ <++> prig <+> "_" <++> colon <++> parg)
                      <++> "->" <+> line <+> pret)
              rig
            Just n =>
              braces (auto_ <++> prig <+> pretty n <++> colon <++> parg)
                      <++> "->" <+> line <+> pret
      go d (PPi _ rig (DefImplicit t) Nothing arg ret) =
        pure $ parenthesise (d > startPrec) $ group $
          braces (default_ <++> !(go appPrec t) <++> prettyRig rig <+> "_"
            <++> colon <++> !(go startPrec arg))
            <++> "->" <+> line <+> !(go startPrec ret)
      go d (PPi _ rig (DefImplicit t) (Just n) arg ret) =
        pure $ parenthesise (d > startPrec) $ group $
          braces (default_ <++> !(go appPrec t) <++> prettyRig rig <+> pretty n
           <++> colon <++> !(go startPrec arg))
           <++> "->" <+> line <+> !(go startPrec ret)
      go d (PLam _ rig _ n ty sc) =
          let (ns, sc) = getLamNames [(rig, n, ty)] sc in
          pure $ parenthesise (d > startPrec) $ group $ align $ hang 2 $
                backslash <+> !(prettyBindings ns) <++> "=>" <+> line <+> !(go startPrec sc)
        where
          getLamNames : List (RigCount, PTerm, PTerm) -> PTerm -> (List (RigCount, PTerm, PTerm), PTerm)
          getLamNames acc (PLam _ rig _ n ty sc) = getLamNames ((rig, n, ty) :: acc) sc
          getLamNames acc sc = (reverse acc, sc)
          prettyBindings : List (RigCount, PTerm, PTerm) -> Core (Doc IdrisSyntax)
          prettyBindings [] = pure neutral
          prettyBindings [(rig, n, (PImplicit _))] =
            pure $ prettyRig rig <+> !(go startPrec n)
          prettyBindings [(rig, n, ty)] =
            pure $ prettyRig rig <+> !(go startPrec n)
                   <++> colon <++> !(go startPrec ty)
          prettyBindings ((rig, n, (PImplicit _)) :: ns) =
            pure $ prettyRig rig <+> !(go startPrec n)
                   <+> comma <+> line <+> !(prettyBindings ns)
          prettyBindings ((rig, n, ty) :: ns) =
            pure $ prettyRig rig <+> !(go startPrec n)
                   <++> colon <++> !(go startPrec ty)
                   <+> comma <+> line <+> !(prettyBindings ns)
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

          continuation : Core (Doc IdrisSyntax)
          continuation = go startPrec sc

          fullLet : Core (Doc IdrisSyntax)
          fullLet = pure $ parenthesise (d > startPrec) $ group $ align $
            let_ <++> (group $ align $ hang 2 $ prettyRig rig <+> !(go startPrec n)
              <++> equals <+> line <+> !(go startPrec val)) <+> line
              <+> in_ <++> (group $ align $ hang 2 $ !continuation)

          getPRefName : PTerm -> Maybe Name
          getPRefName (PRef _ n) = Just n
          getPRefName _ = Nothing

      go d (PLet _ rig n ty val sc alts) =
        pure $ parenthesise (d > startPrec) $ group $ align $
          let_ <++> (group $ align $ hang 2 $ prettyRig rig <+> !(go startPrec n)
                     <++> colon <++> !(go startPrec ty)
                     <++> equals <+> line <+> !(go startPrec val))
            <+> hardline
            <+> hang 4 (fillSep !(traverse prettyAlt alts))
            <+> line <+> in_ <++> (group $ align $ hang 2 $ !(go startPrec sc))
      go d (PCase _ tm cs) =
        pure $ parenthesise (d > appPrec) $
          align $ case_ <++> !(go startPrec tm) <++> of_ <+> line <+>
          braces (vsep $ punctuate semi !(traverse prettyCase cs))
      go d (PLocal _ ds sc) =
        pure $ parenthesise (d > startPrec) $ group $ align $
          let_ <++> braces (angles (angles "definitions"))
          <+> line <+> in_ <++> !(go startPrec sc)
      go d (PUpdate _ fs) =
        pure $ parenthesise (d > appPrec) $ group $
          record_ <++> braces (vsep $ punctuate comma !(traverse prettyUpdate fs))
      go d (PApp _ f a) = case f of
          (PRef _ n) =>
            if isJust (isRF n)
            then pure $ parenthesise (d > appPrec) $ group
                      $ !(go leftAppPrec a) <++> !(go appPrec f)
            else pure $ parenthesise (d > appPrec) $ group
                      $ !(go leftAppPrec f) <++> !(go appPrec a)
          _ => pure $ parenthesise (d > appPrec) $ group
                    $ !(go leftAppPrec f) <++> !(go appPrec a)
      go d (PWithApp _ f a) = pure $ !(go d f) <++> pipe <++> !(go d a)
      go d (PDelayed _ LInf ty) =
        pure $ parenthesise (d > appPrec) $ "Inf" <++> !(go appPrec ty)
      go d (PDelayed _ _ ty) =
        pure $ parenthesise (d > appPrec) $ "Lazy" <++> !(go appPrec ty)
      go d (PDelay _ tm) =
        pure $ parenthesise (d > appPrec) $ "Delay" <++> !(go appPrec tm)
      go d (PForce _ tm) =
        pure $ parenthesise (d > appPrec) $ "Force" <++> !(go appPrec tm)
      go d (PAutoApp _ f a) =
        pure $ parenthesise (d > appPrec) $ group $
          !(go leftAppPrec f) <++> "@" <+> braces !(go startPrec a)
      go d (PNamedApp _ f n (PRef _ a)) = do
        pf <- go leftAppPrec f
        pure $ parenthesise (d > appPrec) $ group $
          if n == a
             then pf <++> braces (pretty n)
             else pf <++> braces (pretty n <++> equals <++> pretty a)
      go d (PNamedApp _ f n a) =
        pure $  parenthesise (d > appPrec) $ group $
          !(go leftAppPrec f) <++> braces (pretty n <++> equals <++> !(go d a))
      go d (PSearch _ _) = pure $ pragma "%search"
      go d (PQuote _ tm) =
        pure $ parenthesise (d > appPrec) $ "`" <+> parens !(go startPrec tm)
      go d (PQuoteName _ n) =
        pure $ parenthesise (d > appPrec) $ "`" <+> braces (braces (pretty n))
      go d (PQuoteDecl _ tm) =
        pure $ parenthesise (d > appPrec) $ "`" <+> brackets (angles (angles (pretty "declaration")))
      go d (PUnquote _ tm) =
        pure $ parenthesise (d > appPrec) $ "~" <+> parens !(go startPrec tm)
      go d (PRunElab _ tm) =
        pure $ parenthesise (d > appPrec) $ pragma "%runElab" <++> !(go startPrec tm)
      go d (PPrimVal _ c) =
        pure $ if isPrimType c
               then annotate (SynDecor Typ) (pretty c)
               else annotate (SynDecor Data) (pretty c)
      go d (PHole _ _ n) = pure $ hole (pretty (strCons '?' n))
      go d (PType _) = pure $ annotate (SynDecor Typ) $ pretty "Type"
      go d (PAs _ _ n p) = pure $ pretty n <+> "@" <+> !(go d p)
      go d (PDotted _ p) = pure $ dot <+> !(go d p)
      go d (PImplicit _) = pure "_"
      go d (PInfer _) = pure "?"
      go d (POp _ _ op x y) =
        pure $ parenthesise (d > appPrec) $ group $
          !(go startPrec x) <++> prettyOp op <++> !(go startPrec y)
      go d (PPrefixOp _ _ op x) =
        pure $ parenthesise (d > appPrec) $ pretty op <+> !(go startPrec x)
      go d (PSectionL _ _ op x) =
        pure $ parens (prettyOp op <++> !(go startPrec x))
      go d (PSectionR _ _ x op) =
        pure $ parens (!(go startPrec x) <++> prettyOp op)
      go d (PEq fc l r) =
        pure $ parenthesise (d > appPrec) $
          !(go startPrec l) <++> equals <++> !(go startPrec r)
      go d (PBracketed _ tm) = pure $ parens !(go startPrec tm)
      go d (PString _ xs) =
        pure $ parenthesise (d > appPrec) $
          hsep $ punctuate "++" !(traverse prettyString xs)
      go d (PMultiline _ indent xs) =
        pure $ "multiline" <++> (parenthesise (d > appPrec) $
          hsep $ punctuate "++" !(traverse prettyString $ concat xs))
      go d (PDoBlock _ ns ds) =
        pure $ parenthesise (d > appPrec) $ group $ align $
           hang 2 $ do_ <++> (vsep $ punctuate semi !(traverse prettyDo ds))
      go d (PBang _ tm) = pure $ "!" <+> !(go d tm)
      go d (PIdiom _ tm) =
        pure $ enclose (pretty "[|") (pretty "|]") !(go startPrec tm)
      go d (PList _ _ xs) =
        pure $ brackets $ group $ align $ vsep $
          punctuate comma !(traverse (go startPrec . snd) xs)
      go d (PSnocList _ _ xs) =
         pure $ brackets {ldelim = "[<"} $ group $ align $ vsep $
           punctuate comma !(traverse (go startPrec . snd) xs)
      go d (PPair _ l r) =
        pure $ group $ parens $
          !(go startPrec l) <+> comma <+> line <+> !(go startPrec r)
      go d (PDPair _ _ l (PImplicit _) r) =
        pure $ group $ parens $
          !(go startPrec l) <++> pretty "**" <+> line <+> !(go startPrec r)
      go d (PDPair _ _ l ty r) =
        pure $ group $ parens $
          !(go startPrec l) <++> colon <++> !(go startPrec ty)
            <++> "**" <+> line <+> !(go startPrec r)
      go d (PUnit _) = pure "()"
      go d (PIfThenElse _ x t e) =
        pure $ parenthesise (d > appPrec) $ group $ align $ hang 2 $ vsep
          [ keyword "if" <++> !(go startPrec x)
          , keyword "then" <++> !(go startPrec t)
          , keyword "else" <++> !(go startPrec e)]
      go d (PComprehension _ ret es) =
          pure $ group $ brackets $
            !(go startPrec (dePure ret)) <++> pipe
             <++> vsep (punctuate comma ! (traverse (prettyDo . deGuard) es))
        where
          dePure : PTerm -> PTerm
          dePure tm@(PApp _ (PRef _ n) arg) = if dropNS n == UN "pure" then arg else tm
          dePure tm = tm

          deGuard : PDo -> PDo
          deGuard tm@(DoExp fc (PApp _ (PRef _ n) arg)) = if dropNS n == UN "guard" then DoExp fc arg else tm
          deGuard tm = tm
      go d (PRewrite _ rule tm) =
        pure $ parenthesise (d > appPrec) $ group $
          rewrite_ <++> !(go startPrec rule)
           <+> line <+> in_ <++> !(go startPrec tm)
      go d (PRange _ start Nothing end) =
        pure $ brackets $
          !(go startPrec start) <++> pretty ".." <++> !(go startPrec end)
      go d (PRange _ start (Just next) end) =
        pure $ brackets $
          !(go startPrec start)
           <+> comma <++> !(go startPrec next)
           <++> pretty ".." <++> !(go startPrec end)
      go d (PRangeStream _ start Nothing) =
        pure $ brackets $ !(go startPrec start) <++> pretty ".."
      go d (PRangeStream _ start (Just next)) =
        pure $ brackets $
          !(go startPrec start)
          <+> comma <++> !(go startPrec next)
          <++> pretty ".."
      go d (PUnifyLog _ lvl tm) = go d tm
      go d (PPostfixApp fc rec fields) =
        pure $ parenthesise (d > appPrec) $
          !(go startPrec rec) <++>
           dot <+> concatWith (surround dot) (map pretty fields)
      go d (PPostfixAppPartial fc fields) =
        pure $ parens (dot <+> concatWith (surround dot) (map pretty fields))
      go d (PWithUnambigNames fc ns rhs) =
        pure $ parenthesise (d > appPrec) $ group $
          with_ <++> pretty ns <+> line <+> !(go startPrec rhs)

export
render : {auto o : Ref ROpts REPLOpts} -> Doc IdrisAnn -> Core String
render = render colorAnn
