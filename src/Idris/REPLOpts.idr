module Idris.REPLOpts

import Compiler.Common
import Idris.Syntax
import Parser.Unlit
import TTImp.Interactive.ExprSearch
import TTImp.TTImp

import Data.List
import Data.Strings
import System.File

%default total

public export
data OutputMode
  = IDEMode Integer File File
  | REPL Bool -- quiet flag (ignore iputStrLn)

public export
record REPLOpts where
  constructor MkREPLOpts
  showTypes : Bool
  evalMode : REPLEval
  mainfile : Maybe String
  literateStyle : Maybe LiterateStyle
  source : String
  editor : String
  errorLine : Maybe Int
  idemode : OutputMode
  currentElabSource : String
  psResult : Maybe (Name, Core (Search RawImp)) -- last proof search continuation (and name)
  gdResult : Maybe (Int, Core (Search (FC, List ImpClause))) -- last generate def continuation (and line number)
  -- TODO: Move extraCodegens from here, it doesn't belong, but there's nowhere
  -- better to stick it now.
  extraCodegens : List (String, Codegen)
  consoleWidth : Maybe Nat -- Nothing is auto
  color : Bool

export
defaultOpts : Maybe String -> OutputMode -> List (String, Codegen) -> REPLOpts
defaultOpts fname outmode cgs
    = MkREPLOpts False NormaliseAll fname (litStyle fname) "" "vim"
                 Nothing outmode "" Nothing Nothing cgs Nothing True
  where
    litStyle : Maybe String -> Maybe LiterateStyle
    litStyle Nothing = Nothing
    litStyle (Just fn) = isLitFile fn

export
data ROpts : Type where

export
replFC : FC
replFC = MkFC "(interactive)" (0, 0) (0, 0)

export
setOutput : {auto o : Ref ROpts REPLOpts} ->
            OutputMode -> Core ()
setOutput m
    = do opts <- get ROpts
         put ROpts (record { idemode = m } opts)

export
getOutput : {auto o : Ref ROpts REPLOpts} -> Core OutputMode
getOutput = do opts <- get ROpts
               pure (idemode opts)

export
setMainFile : {auto o : Ref ROpts REPLOpts} ->
              Maybe String -> Core ()
setMainFile src
    = do opts <- get ROpts
         put ROpts (record { mainfile = src,
                             literateStyle = litStyle src } opts)
  where
    litStyle : Maybe String -> Maybe LiterateStyle
    litStyle Nothing = Nothing
    litStyle (Just fn) = isLitFile fn

export
resetProofState : {auto o : Ref ROpts REPLOpts} ->
                  Core ()
resetProofState
    = do opts <- get ROpts
         put ROpts (record { psResult = Nothing,
                             gdResult = Nothing } opts)

export
setSource : {auto o : Ref ROpts REPLOpts} ->
            String -> Core ()
setSource src
    = do opts <- get ROpts
         put ROpts (record { source = src } opts)

export
getSource : {auto o : Ref ROpts REPLOpts} ->
            Core String
getSource
    = do opts <- get ROpts
         pure (source opts)

export
getSourceLine : {auto o : Ref ROpts REPLOpts} ->
                Int -> Core (Maybe String)
getSourceLine l
    = do src <- getSource
         pure $ findLine (integerToNat (cast (l-1))) (lines src)
  where
    findLine : Nat -> List String -> Maybe String
    findLine Z (l :: ls) = Just l
    findLine (S k) (l :: ls) = findLine k ls
    findLine _ [] = Nothing

export
getLitStyle : {auto o : Ref ROpts REPLOpts} ->
              Core (Maybe LiterateStyle)
getLitStyle
    = do opts <- get ROpts
         pure (literateStyle opts)

export
setCurrentElabSource : {auto o : Ref ROpts REPLOpts} ->
                       String -> Core ()
setCurrentElabSource src
    = do opts <- get ROpts
         put ROpts (record { currentElabSource = src } opts)

export
getCurrentElabSource : {auto o : Ref ROpts REPLOpts} ->
                       Core String
getCurrentElabSource
     = do opts <- get ROpts
          pure (currentElabSource opts)

addCodegen : {auto o : Ref ROpts REPLOpts} ->
             String -> Codegen -> Core ()
addCodegen s cg = do opts <- get ROpts
                     put ROpts (record { extraCodegens $= ((s,cg)::) } opts)

export
getCodegen : {auto o : Ref ROpts REPLOpts} ->
             String -> Core (Maybe Codegen)
getCodegen s = do opts <- get ROpts
                  pure $ lookup s (extraCodegens opts)

export
getConsoleWidth : {auto o : Ref ROpts REPLOpts} -> Core (Maybe Nat)
getConsoleWidth = do opts <- get ROpts
                     pure $ opts.consoleWidth

export
setConsoleWidth : {auto o : Ref ROpts REPLOpts} -> Maybe Nat -> Core ()
setConsoleWidth n = do opts <- get ROpts
                       put ROpts (record { consoleWidth = n } opts)

export
getColor : {auto o : Ref ROpts REPLOpts} -> Core Bool
getColor = do opts <- get ROpts
              pure $ opts.color

export
setColor : {auto o : Ref ROpts REPLOpts} -> Bool -> Core ()
setColor b = do opts <- get ROpts
                put ROpts (record { color = b } opts)
