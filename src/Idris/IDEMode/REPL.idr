module Idris.IDEMode.REPL

import Compiler.Scheme.Chez
import Compiler.Scheme.Racket
import Compiler.Scheme.Gambit
import Compiler.Common

import Core.AutoSearch
import Core.CompileExpr
import Core.Context
import Core.InitPrimitives
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.TT
import Core.Unify

import Idris.Desugar
import Idris.Error
import Idris.ModTree
import Idris.Parser
import Idris.Resugar
import Idris.REPL
import Idris.Syntax
import Idris.Version

import Idris.IDEMode.Parser
import Idris.IDEMode.Commands
import Idris.IDEMode.SyntaxHighlight

import TTImp.Interactive.CaseSplit
import TTImp.Elab
import TTImp.TTImp
import TTImp.ProcessDecls

import Utils.Hex

import Data.List
import System

import Network.Socket
import Network.Socket.Data

%foreign "C:fdopen,libc 6"
prim__fdopen : Int -> String -> PrimIO AnyPtr

export
socketToFile : Socket -> IO (Either String File)
socketToFile (MkSocket f _ _ _) = do
  file <- FHandle <$> primIO (prim__fdopen f "r+")
  if !(fileError file)
    then pure (Left "Failed to fdopen socket file descriptor")
    else pure (Right file)

export
initIDESocketFile : String -> Int -> IO (Either String File)
initIDESocketFile h p = do
  osock <- socket AF_INET Stream 0
  case osock of
    Left fail => do
      putStrLn (show fail)
      putStrLn "Failed to open socket"
      exitWith (ExitFailure 1)
    Right sock => do
      res <- bind sock (Just (Hostname h)) p
      if res /= 0
        then pure (Left ("Failed to bind socket with error: " ++ show res))
        else 
          do res <- listen sock
             if res /= 0
                then
                  pure (Left ("Failed to listen on socket with error: " ++ show res))
               else 
                 do putStrLn (show p)
                    res <- accept sock
                    case res of
                      Left err =>
                         pure (Left ("Failed to accept on socket with error: " ++ show err))
                      Right (s, _) =>
                         socketToFile s

getChar : File -> IO Char
getChar h = do
  if !(fEOF h)
     then do
       putStrLn "Alas the file is done, aborting"
       exitWith (ExitFailure 1)
     else do
       Right chr <- fGetChar h
           | Left err => do putStrLn "Failed to read a character"
                            exitWith (ExitFailure 1)
       pure chr

getFLine : File -> IO String
getFLine h
    = do Right str <- fGetLine h
               | Left err =>
                   do putStrLn "Failed to read a line"
                      exitWith (ExitFailure 1)
         pure str

getNChars : File -> Nat -> IO (List Char)
getNChars i Z = pure []
getNChars i (S k)
    = do x <- getChar i
         xs <- getNChars i k
         pure (x :: xs)

-- Read 6 characters. If they're a hex number, read that many characters.
-- Otherwise, just read to newline
getInput : File -> IO String
getInput f
    = do x <- getNChars f 6
         case fromHexChars (reverse x) of
              Nothing =>
                do rest <- getFLine f
                   pure (pack x ++ rest)
              Just num =>
                do inp <- getNChars f (integerToNat (cast num))
                   pure (pack inp)


process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref MD Metadata} ->
          {auto o : Ref ROpts REPLOpts} ->
          IDECommand -> Core REPLResult
process (Interpret cmd)
    = interpret cmd
process (LoadFile fname _)
    = Idris.REPL.process (Load fname) >>= outputSyntaxHighlighting fname
process (TypeOf n Nothing)
    = Idris.REPL.process (Check (PRef replFC (UN n)))
process (TypeOf n (Just (l, c)))
    = Idris.REPL.process (Editing (TypeAt (fromInteger l) (fromInteger c) (UN n)))
process (CaseSplit l c n)
    = Idris.REPL.process (Editing (CaseSplit False (fromInteger l) (fromInteger c) (UN n)))
process (AddClause l n)
    = Idris.REPL.process (Editing (AddClause False (fromInteger l) (UN n)))
process (ExprSearch l n hs all)
    = Idris.REPL.process (Editing (ExprSearch False (fromInteger l) (UN n)
                                                 (map UN hs) all))
process (GenerateDef l n)
    = Idris.REPL.process (Editing (GenerateDef False (fromInteger l) (UN n)))
process (MakeLemma l n)
    = Idris.REPL.process (Editing (MakeLemma False (fromInteger l) (UN n)))
process (MakeCase l n)
    = Idris.REPL.process (Editing (MakeCase False (fromInteger l) (UN n)))
process (MakeWith l n)
    = Idris.REPL.process (Editing (MakeWith False (fromInteger l) (UN n)))
process Version
    = Idris.REPL.process ShowVersion
process (Metavariables _)
    = Idris.REPL.process Metavars
process GetOptions
    = Idris.REPL.process GetOpts

processCatch : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref MD Metadata} ->
               {auto o : Ref ROpts REPLOpts} ->
               IDECommand -> Core REPLResult
processCatch cmd
    = do c' <- branch
         u' <- get UST
         s' <- get Syn
         o' <- get ROpts
         catch (do res <- process cmd
                   commit
                   pure res)
               (\err => do put Ctxt c'
                           put UST u'
                           put Syn s'
                           put ROpts o'
                           msg <- perror err
                           pure $ REPLError msg)

idePutStrLn : File -> Integer -> String -> Core ()
idePutStrLn outf i msg
    = send outf (SExpList [SymbolAtom "write-string",
                toSExp msg, toSExp i])

returnFromIDE : File -> Integer -> SExp -> Core ()
returnFromIDE outf i msg
    = do send outf (SExpList [SymbolAtom "return", msg, toSExp i])

printIDEResult : File -> Integer -> SExp -> Core ()
printIDEResult outf i msg = returnFromIDE outf i (SExpList [SymbolAtom "ok", toSExp msg])

printIDEResultWithHighlight : File -> Integer -> SExp -> Core ()
printIDEResultWithHighlight outf i msg = returnFromIDE outf i (SExpList [SymbolAtom "ok", toSExp msg
                                                                        -- TODO return syntax highlighted result
                                                                        , SExpList []])

printIDEError : File -> Integer -> String -> Core ()
printIDEError outf i msg = returnFromIDE outf i (SExpList [SymbolAtom "error", toSExp msg ])

SExpable REPLEval where
  toSExp EvalTC = SymbolAtom "typecheck"
  toSExp NormaliseAll = SymbolAtom "normalise"
  toSExp Execute = SymbolAtom "execute"

SExpable REPLOpt where
  toSExp (ShowImplicits impl) = SExpList [ SymbolAtom "show-implicits", toSExp impl ]
  toSExp (ShowNamespace ns) = SExpList [ SymbolAtom "show-namespace", toSExp ns ]
  toSExp (ShowTypes typs) = SExpList [ SymbolAtom "show-types", toSExp typs ]
  toSExp (EvalMode mod) = SExpList [ SymbolAtom "eval", toSExp mod ]
  toSExp (Editor editor) = SExpList [ SymbolAtom "editor", toSExp editor ]
  toSExp (CG str) = SExpList [ SymbolAtom "cg", toSExp str ]


sexpName :  Name -> SExp
sexpName n = SExpList [ StringAtom (show  n), SExpList [], SExpList [] ]

displayIDEResult : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST UState} ->
       {auto s : Ref Syn SyntaxInfo} ->
       {auto m : Ref MD Metadata} ->
       {auto o : Ref ROpts REPLOpts} ->
       File -> Integer -> REPLResult -> Core ()
displayIDEResult outf i  (REPLError err) = printIDEError outf i err
displayIDEResult outf i  (Evaluated x Nothing) = printIDEResultWithHighlight outf i $ StringAtom $ show x
displayIDEResult outf i  (Evaluated x (Just y)) = printIDEResultWithHighlight outf i $ StringAtom $ show x ++ " : " ++ show y
displayIDEResult outf i  (Printed xs) = printIDEResultWithHighlight outf i $ StringAtom $ showSep "\n" xs
displayIDEResult outf i  (TermChecked x y) = printIDEResultWithHighlight outf i $ StringAtom $ show x ++ " : " ++ show y
displayIDEResult outf i  (FileLoaded x) = printIDEResult outf i $ SExpList []
displayIDEResult outf i  (ErrorLoadingFile x err) = printIDEError outf i $ "Error loading file " ++ x ++ ": " ++ show err
displayIDEResult outf i  (ErrorsBuildingFile x errs) = printIDEError outf i $ "Error(s) building file " ++ x ++ ": " ++ (showSep "\n" $ map show errs)
displayIDEResult outf i  NoFileLoaded = printIDEError outf i "No file can be reloaded"
displayIDEResult outf i  (CurrentDirectory dir) = printIDEResult outf i $ StringAtom $ "Current working directory is '" ++ dir ++ "'"
displayIDEResult outf i  CompilationFailed = printIDEError outf i "Compilation failed"
displayIDEResult outf i  (Compiled f) = printIDEResult outf i $ StringAtom $ "File " ++ f ++ " written"
displayIDEResult outf i  (ProofFound x) = printIDEResult outf i $ StringAtom $ show x
--displayIDEResult outf i  (Missed cases) = printIDEResult outf i $ showSep "\n" $ map handleMissing cases
displayIDEResult outf i  (CheckedTotal xs) = printIDEResult outf i $ StringAtom $ showSep "\n" $ map (\ (fn, tot) => (show fn ++ " is " ++ show tot)) xs
displayIDEResult outf i  (FoundHoles []) = printIDEResult outf i $ SExpList []
displayIDEResult outf i  (FoundHoles xs) = printIDEResult outf i $ holesSexp
  where
    holesSexp : SExp
    holesSexp = SExpList $ map sexpName xs

displayIDEResult outf i  (LogLevelSet k) = printIDEResult outf i $ StringAtom $ "Set loglevel to " ++ show k
displayIDEResult outf i  (OptionsSet opts) = printIDEResult outf i optionsSexp
  where
    optionsSexp : SExp
    optionsSexp = SExpList $ map toSExp opts
displayIDEResult outf i  (VersionIs x) = printIDEResult outf i versionSExp
  where
  semverSexp : SExp
  semverSexp = case (semVer x) of
                  (maj, min, patch) => SExpList (map toSExp [maj, min, patch])
  tagSexp : SExp
  tagSexp = case versionTag x of
              Nothing => SExpList [ StringAtom "" ]
              Just t => SExpList [ StringAtom t ]
  versionSExp : SExp
  versionSExp = SExpList [ semverSexp, tagSexp ]


displayIDEResult outf i  (Edited (DisplayEdit xs)) = printIDEResult outf i $ StringAtom $ showSep "\n" xs
displayIDEResult outf i  (Edited (EditError x)) = printIDEError outf i x
displayIDEResult outf i  (Edited (MadeLemma lit name pty pappstr)) =
  printIDEResult outf i $ StringAtom $ (relit lit $ show name ++ " : " ++ show pty ++ "\n") ++ pappstr
displayIDEResult outf i  _ = pure ()


handleIDEResult : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST UState} ->
       {auto s : Ref Syn SyntaxInfo} ->
       {auto m : Ref MD Metadata} ->
       {auto o : Ref ROpts REPLOpts} ->
       File -> Integer -> REPLResult -> Core ()
handleIDEResult outf i Exited = idePutStrLn outf i "Bye for now!"
handleIDEResult outf i other = displayIDEResult outf i other

loop : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST UState} ->
       {auto s : Ref Syn SyntaxInfo} ->
       {auto m : Ref MD Metadata} ->
       {auto o : Ref ROpts REPLOpts} ->
       Core ()
loop
    = do res <- getOutput
         case res of
              REPL _ => printError "Running idemode but output isn't"
              IDEMode idx inf outf => do
                inp <- coreLift $ getInput inf
                end <- coreLift $ fEOF inf
                if end 
                   then pure ()
                   else case parseSExp inp of
                      Left err =>
                        do printIDEError outf idx ("Parse error: " ++ show err)
                           loop
                      Right sexp =>
                        case getMsg sexp of
                          Just (cmd, i) =>
                            do updateOutput i
                               res <- processCatch cmd
                               handleIDEResult outf i res
                               loop
                          Nothing =>
                            do printIDEError outf idx ("Unrecognised command: " ++ show sexp)
                               loop
  where
    updateOutput : Integer -> Core ()
    updateOutput idx
        = do IDEMode _ i o <- getOutput
                 | _ => pure ()
             setOutput (IDEMode idx i o)

export
replIDE : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref MD Metadata} ->
          {auto o : Ref ROpts REPLOpts} ->
          Core ()
replIDE
    = do res <- getOutput
         case res of
              REPL _ => printError "Running idemode but output isn't"
              IDEMode _ inf outf => do
                send outf (version 2 0)
                loop
