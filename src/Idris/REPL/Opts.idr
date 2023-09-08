module Idris.REPL.Opts

import Compiler.Common
import Idris.Syntax
import Parser.Unlit
import TTImp.TTImp

import Data.List
import Data.List1
import Libraries.Data.List.Extra
import Libraries.Data.Tap
import Data.String
import System.File

%default total

namespace VerbosityLvl
  public export
  data VerbosityLvl =
   ||| Suppress all message output to `stdout`.
   NoneLvl |
   ||| Keep only errors.
   ErrorLvl |
   ||| Keep everything.
   InfoLvl

public export
data OutputMode
  = IDEMode Integer File File |
    ||| Given that we can divide elaboration messages into
    ||| two categories: informational message and error message,
    ||| `VerbosityLvl` applies a filter on the output,
    |||  suppressing writes to `stdout` if the level condition isn't met.
    REPL VerbosityLvl

public export
record REPLOpts where
  constructor MkREPLOpts
  showTypes : Bool
  evalMode : REPLEval
  evalTiming : Bool
  mainfile : Maybe String
  literateStyle : Maybe LiterateStyle
  source : String
  editor : String
  errorLine : Maybe Int
  idemode : OutputMode
  currentElabSource : String
  psResult : Maybe (Name, Core (Search RawImp)) -- last proof search continuation (and name)
  gdResult : Maybe (Int, Core (Search (FC, List ImpClause))) -- last generate def continuation (and line number)
  evalResultName : Maybe Name
  -- TODO: Move extraCodegens from here, it doesn't belong, but there's nowhere
  -- better to stick it now.
  extraCodegens : List (String, Codegen)
  consoleWidth : Maybe Nat -- Nothing is auto
  color : Bool
  synHighlightOn : Bool

litStyle : Maybe String -> Maybe LiterateStyle
litStyle = join . map isLitFile

covering
export
defaultOpts : Maybe String -> OutputMode -> List (String, Codegen) -> REPLOpts
defaultOpts fname outmode cgs
    = MkREPLOpts
        { showTypes = False
        , evalMode = NormaliseAll
        , evalTiming = False
        , mainfile = fname
        , literateStyle = litStyle fname
        , source = ""
        , editor = "vim"
        , errorLine = Nothing
        , idemode = outmode
        , currentElabSource = ""
        , psResult = Nothing
        , gdResult = Nothing
        , evalResultName = Nothing
        , extraCodegens = cgs
        , consoleWidth = Nothing
        , color = True
        , synHighlightOn = True
        }
  where
    litStyle : Maybe String -> Maybe LiterateStyle
    litStyle Nothing = Nothing
    litStyle (Just fn) = isLitFile fn

export
data ROpts : Type where

export
withROpts : {auto o : Ref ROpts REPLOpts} -> Core a -> Core a
withROpts = wrapRef ROpts (\_ => pure ())

export
setOutput : {auto o : Ref ROpts REPLOpts} ->
            OutputMode -> Core ()
setOutput m = update ROpts { idemode := m }

export
getOutput : {auto o : Ref ROpts REPLOpts} -> Core OutputMode
getOutput = idemode <$> get ROpts

export
setMainFile : {auto o : Ref ROpts REPLOpts} ->
              Maybe String -> Core ()
setMainFile src = update ROpts { mainfile      := src,
                                 literateStyle := litStyle src }

covering
export
resetProofState : {auto o : Ref ROpts REPLOpts} -> Core ()
resetProofState = update ROpts { psResult := Nothing,
                                 gdResult := Nothing }

export
setSource : {auto o : Ref ROpts REPLOpts} ->
            String -> Core ()
setSource src = update ROpts { source := src }

export
getSource : {auto o : Ref ROpts REPLOpts} ->
            Core String
getSource = source <$> get ROpts

export
getSourceLine : {auto o : Ref ROpts REPLOpts} ->
                Int -> Core (Maybe String)
getSourceLine l
    = do src <- getSource
         pure $ elemAt (lines src) (integerToNat (cast (l-1)))

export
getLitStyle : {auto o : Ref ROpts REPLOpts} ->
              Core (Maybe LiterateStyle)
getLitStyle = literateStyle <$> get ROpts

export
setCurrentElabSource : {auto o : Ref ROpts REPLOpts} ->
                       String -> Core ()
setCurrentElabSource src = update ROpts { currentElabSource := src }

export
getCurrentElabSource : {auto o : Ref ROpts REPLOpts} ->
                       Core String
getCurrentElabSource = currentElabSource <$> get ROpts

addCodegen : {auto o : Ref ROpts REPLOpts} ->
             String -> Codegen -> Core ()
addCodegen s cg = update ROpts { extraCodegens $= ((s,cg)::) }

export
getCodegen : {auto o : Ref ROpts REPLOpts} ->
             String -> Core (Maybe Codegen)
getCodegen s = lookup s . extraCodegens <$> get ROpts

export
getConsoleWidth : {auto o : Ref ROpts REPLOpts} -> Core (Maybe Nat)
getConsoleWidth = consoleWidth <$> get ROpts

export
setConsoleWidth : {auto o : Ref ROpts REPLOpts} -> Maybe Nat -> Core ()
setConsoleWidth n = update ROpts { consoleWidth := n }

export
getColor : {auto o : Ref ROpts REPLOpts} -> Core Bool
getColor = color <$> get ROpts

export
setColor : {auto o : Ref ROpts REPLOpts} -> Bool -> Core ()
setColor b = update ROpts { color := b }

export
getSynHighlightOn : {auto o : Ref ROpts REPLOpts} -> Core Bool
getSynHighlightOn = synHighlightOn <$> get ROpts

export
setSynHighlightOn : {auto o : Ref ROpts REPLOpts} -> Bool -> Core ()
setSynHighlightOn b = update ROpts { synHighlightOn := b }

export
getEvalTiming : {auto o : Ref ROpts REPLOpts} -> Core Bool
getEvalTiming = evalTiming <$> get ROpts

export
setEvalTiming : {auto o : Ref ROpts REPLOpts} -> Bool -> Core ()
setEvalTiming b = update ROpts { evalTiming := b }
