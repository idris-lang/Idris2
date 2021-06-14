module Idris.Doc.HTML

import Core.Context
import Core.Core
import Core.Directory

import Data.Strings

import Parser.Lexer.Source

import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Render.HTML
import Libraries.Text.PrettyPrint.Prettyprinter.SimpleDocTree

import Idris.Doc.String
import Idris.Package.Types
import Idris.Pretty
import Idris.Version

%default covering

getNS : Name -> String
getNS (NS ns _) = show ns
getNS _ = ""

hasNS : Name -> Bool
hasNS (NS _ _) = True
hasNS _ = False

tryCanonicalName : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core (Maybe Name)
tryCanonicalName fc n with (hasNS n)
  tryCanonicalName fc n | True
      = do defs <- get Ctxt
           case !(lookupCtxtName n (gamma defs)) of
                [(n, _, _)] => pure $ Just n
                _ => pure Nothing
  tryCanonicalName fc n | False = pure Nothing

packageInternal : {auto c : Ref Ctxt Defs} ->
                  Name -> Core Bool
packageInternal (NS ns _) =
  do let mi = nsAsModuleIdent ns
     catch ((const True) <$> nsToSource emptyFC mi) (\_ => pure False)
packageInternal _ = pure False

prettyNameRoot : Name -> String
prettyNameRoot n =
  let root = htmlEscape $ nameRoot n in
  if isOpName n then "(" ++ root ++ ")" else root

renderHtml : {auto c : Ref Ctxt Defs} ->
             SimpleDocTree IdrisDocAnn ->
             Core String
renderHtml STEmpty = pure neutral
renderHtml (STChar ' ') = pure "&ensp;"
renderHtml (STChar c) = pure $ cast c
renderHtml (STText _ text) = pure $ htmlEscape text
renderHtml (STLine _) = pure "<br>"
renderHtml (STAnn Declarations rest) = pure $ "<dl class=\"decls\">" <+> !(renderHtml rest) <+> "</dl>"
renderHtml (STAnn (Decl n) rest) = pure $ "<dt id=\"" ++ (htmlEscape $ show n) ++ "\">" <+> !(renderHtml rest) <+> "</dt>"
renderHtml (STAnn DocStringBody rest) = pure $ "<dd>" <+> !(renderHtml rest) <+> "</dd>"
renderHtml (STAnn DCon rest) = do
  resthtml <- renderHtml rest
  pure $ "<span class=\"name constructor\">" <+> resthtml <+> "</span>"
renderHtml (STAnn (TCon n) rest) = do
  pure $ "<span class=\"name type\">" <+> (prettyNameRoot n) <+> "</span>"
renderHtml (STAnn (Fun n) rest) = do
  pure $ "<span class=\"name function\">" <+> (prettyNameRoot n) <+> "</span>"
renderHtml (STAnn Header rest) = do
  resthtml <- renderHtml rest
  pure $ "<b>" <+> resthtml <+> "</b>"
renderHtml (STAnn (Syntax (SynRef n)) rest) = do
  resthtml <- renderHtml rest
  Just cName <- tryCanonicalName emptyFC n
    | Nothing => pure $ "<span class=\"implicit\">" <+> resthtml <+> "</span>"
  True <- packageInternal cName
    | False => pure $ "<span class=\"type resolved\" title=\"" <+> (htmlEscape $ show cName) <+> "\">" <+> (htmlEscape $ nameRoot cName) <+> "</span>"
  pure $ "<a class=\"type\" href=\"" ++ (htmlEscape $ getNS cName) ++ ".html#" ++ (htmlEscape $ show cName) ++ "\">" <+> (htmlEscape $ nameRoot cName) <+> "</a>"
renderHtml (STAnn ann rest) = do
  resthtml <- renderHtml rest
  pure $ "<!-- ann ignored START -->" ++ resthtml ++ "<!-- ann END -->"
renderHtml (STConcat docs) = pure $ fastConcat !(traverse renderHtml docs)

removeNewlinesFromDeclarations : SimpleDocTree IdrisDocAnn -> SimpleDocTree IdrisDocAnn
removeNewlinesFromDeclarations = go False
  where
    go : Bool -> SimpleDocTree IdrisDocAnn -> SimpleDocTree IdrisDocAnn
    go False l@(STLine i) = l
    go True l@(STLine i) = STEmpty
    go ignoring (STConcat docs) = STConcat $ map (go ignoring) docs
    go _ (STAnn Declarations rest) = STAnn Declarations $ go True rest
    go _ (STAnn ann rest) = STAnn ann $ go False rest
    go _ doc = doc

docDocToHtml : {auto c : Ref Ctxt Defs} ->
               Doc IdrisDocAnn ->
               Core String
docDocToHtml doc =
  let dt = SimpleDocTree.fromStream $ layoutUnbounded doc in
      renderHtml $ removeNewlinesFromDeclarations dt

htmlPreamble : String -> String -> String -> String
htmlPreamble title root class = "<!DOCTYPE html><html lang=\"en\"><head><meta charset=\"utf-8\">"
  ++ "<title>" ++ htmlEscape title ++ "</title>"
  ++ "<link rel=\"stylesheet\" href=\"" ++ root ++ "styles.css\"></head>"
  ++ "<body class=\"" ++ class ++ "\">"
  ++ "<header><strong>Idris2Doc</strong> : " ++ htmlEscape title
  ++ "<nav><a href=\"" ++ root ++ "index.html\">Index</a></nav></header>"
  ++ "<div class=\"container\">"

htmlFooter : String
htmlFooter = "</div><footer>Produced by Idris 2 version " ++ (showVersion True version) ++ "</footer></body></html>"

export
renderDocIndex : PkgDesc -> String
renderDocIndex pkg = fastConcat $
  [ htmlPreamble (name pkg) "" "index"
  , "<h1>Package ", name pkg, " - Namespaces</h1>"
  , "<ul class=\"names\">"] ++
  (map moduleLink $ modules pkg) ++
  [ "</ul>"
  , htmlFooter
  ]
    where
      moduleLink : (ModuleIdent, String) -> String
      moduleLink (mod, filename) =
         "<li><a class=\"code\" href=\"docs/" ++ (show mod) ++ ".html\">" ++ (show mod) ++ "</a></li>"

export
renderModuleDoc : {auto c : Ref Ctxt Defs} ->
                  ModuleIdent ->
                  Doc IdrisDocAnn ->
                  Core String
renderModuleDoc mod allModuleDocs = pure $ fastConcat
  [ htmlPreamble (show mod) "../" "namespace"
  , "<h1>", show mod, "</h1>"
  , !(docDocToHtml allModuleDocs)
  , htmlFooter
  ]
