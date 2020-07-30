module Idris.REPLCommon

import Core.Context
import Core.InitPrimitives
import Core.Metadata
import Core.Options
import Core.Unify

import Idris.Error
import Idris.IDEMode.Commands
import public Idris.REPLOpts
import Idris.Syntax
import Idris.Pretty

import Data.List
import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Render.Terminal

%default covering

-- Output informational messages, unless quiet flag is set
export
iputStrLn : {auto o : Ref ROpts REPLOpts} ->
            Doc IdrisAnn -> Core ()
iputStrLn msg
    = do opts <- get ROpts
         case idemode opts of
              REPL False => coreLift $ putStrLn !(render msg)
              REPL _ => pure ()
              IDEMode i _ f =>
                send f (SExpList [SymbolAtom "write-string",
                                 toSExp !(renderWithoutColor msg), toSExp i])


printWithStatus : {auto o : Ref ROpts REPLOpts} ->
                  Doc IdrisAnn -> Doc IdrisAnn -> Core ()
printWithStatus status msg
    = do opts <- get ROpts
         case idemode opts of
              REPL _ => coreLift $ putStrLn !(render msg)
              _      => pure () -- this function should never be called in IDE Mode

export
printResult : {auto o : Ref ROpts REPLOpts} ->
              Doc IdrisAnn -> Core ()
printResult msg = printWithStatus (pretty "ok") msg

-- Return that a protocol request failed somehow
export
printError : {auto o : Ref ROpts REPLOpts} ->
             Doc IdrisAnn -> Core ()
printError msg = printWithStatus (pretty "error") msg

-- Display an error message from checking a source file
export
emitError : {auto c : Ref Ctxt Defs} ->
            {auto o : Ref ROpts REPLOpts} ->
            {auto s : Ref Syn SyntaxInfo} ->
            Error -> Core ()
emitError err
    = do opts <- get ROpts
         case idemode opts of
              REPL _ =>
                  do msg <- display err >>= render
                     coreLift $ putStrLn msg
              IDEMode i _ f =>
                  do msg <- perror err
                     case getErrorLoc err of
                          Nothing => iputStrLn msg
                          Just fc =>
                            send f (SExpList [SymbolAtom "warning",
                                   SExpList [toSExp (file fc),
                                            toSExp (addOne (startPos fc)),
                                              toSExp (addOne (endPos fc)),
                                              toSExp !(renderWithoutColor msg),
                                              -- highlighting; currently blank
                                              SExpList []],
                                    toSExp i])
  where
    addOne : (Int, Int) -> (Int, Int)
    addOne (l, c) = (l + 1, c + 1)

export
emitWarning : {auto c : Ref Ctxt Defs} ->
              {auto o : Ref ROpts REPLOpts} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Warning -> Core ()
emitWarning w
    = do opts <- get ROpts
         case idemode opts of
              REPL _ =>
                  do msg <- displayWarning w >>= render
                     coreLift $ putStrLn msg
              IDEMode i _ f =>
                  do msg <- pwarning w
                     case getWarningLoc w of
                          Nothing => iputStrLn msg
                          Just fc =>
                            send f (SExpList [SymbolAtom "warning",
                                   SExpList [toSExp (file fc),
                                            toSExp (addOne (startPos fc)),
                                              toSExp (addOne (endPos fc)),
                                              toSExp !(renderWithoutColor msg),
                                              -- highlighting; currently blank
                                              SExpList []],
                                    toSExp i])
  where
    addOne : (Int, Int) -> (Int, Int)
    addOne (l, c) = (l + 1, c + 1)

export
emitWarnings : {auto c : Ref Ctxt Defs} ->
               {auto o : Ref ROpts REPLOpts} ->
               {auto s : Ref Syn SyntaxInfo} ->
               Core ()
emitWarnings
    = do defs <- get Ctxt
         traverse_ emitWarning (reverse (warnings defs))
         put Ctxt (record { warnings = [] } defs)

getFCLine : FC -> Int
getFCLine fc = fst (startPos fc)

export
updateErrorLine : {auto o : Ref ROpts REPLOpts} ->
                  List Error -> Core ()
updateErrorLine []
    = do opts <- get ROpts
         put ROpts (record { errorLine = Nothing } opts)
updateErrorLine (e :: _)
    = do opts <- get ROpts
         put ROpts (record { errorLine = map getFCLine (getErrorLoc e) } opts)

export
resetContext : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref MD Metadata} ->
               Core ()
resetContext
    = do defs <- get Ctxt
         put Ctxt (record { options = clearNames (options defs) } !initDefs)
         addPrimitives
         put UST initUState
         put Syn initSyntax
         put MD initMetadata
