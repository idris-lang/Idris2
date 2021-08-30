module Idris.Pretty.Render

import Core.Core

import Idris.REPL.Opts

import Libraries.Control.ANSI.SGR
import Libraries.Text.PrettyPrint.Prettyprinter
import public Libraries.Text.PrettyPrint.Prettyprinter.Render.Terminal
import Libraries.Utils.Term

import System

%default total

getPageWidth : {auto o : Ref ROpts REPLOpts} -> Core PageWidth
getPageWidth = do
  consoleWidth <- getConsoleWidth
  case consoleWidth of
    Nothing => do
      cols <- coreLift getTermCols
      pure $ if cols == 0 then Unbounded else AvailablePerLine cols 1
    Just 0 => pure $ Unbounded
    Just cw => pure $ AvailablePerLine (cast cw) 1

export
render : {auto o : Ref ROpts REPLOpts} ->
         (ann -> AnsiStyle) ->
         Doc ann -> Core String
render stylerAnn doc = do
  color <- getColor
  isDumb <- (Just "dumb" ==) <$> coreLift (getEnv "TERM")
  -- ^-- emacs sets the TERM variable to `dumb` and expects the compiler
  --     to not emit any ANSI escape codes
  pageWidth <- getPageWidth
  let opts = MkLayoutOptions pageWidth
  let layout = layoutPretty opts doc
  pure $ renderString $
    if color && not isDumb
      then reAnnotateS stylerAnn layout
      else unAnnotateS layout

export
renderWithoutColor : {auto o : Ref ROpts REPLOpts} -> Doc ann -> Core String
renderWithoutColor doc = do
  pageWidth <- getPageWidth
  let opts = MkLayoutOptions pageWidth
  let layout = layoutPretty opts doc
  pure $ renderString $ unAnnotateS layout

export
renderWithSpans : {auto o : Ref ROpts REPLOpts} ->
  Doc ann ->
  Core (String, List (Span ann))
renderWithSpans doc = do
  pageWidth <- getPageWidth
  let opts = MkLayoutOptions pageWidth
  let layout = layoutPretty opts doc
  pure $ displaySpans layout
