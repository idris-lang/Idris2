module Idris.IDEMode.REPL

import Core.Context
import Core.Directory
import Core.Metadata
import Core.Options
import Core.Unify

import Idris.Error
import Idris.Package
import Idris.Parser
import Idris.Pretty
import Idris.REPL
import Idris.Syntax
import Idris.Version
import Idris.Doc.String

import Idris.IDEMode.Commands
import Idris.IDEMode.Holes
import Idris.IDEMode.Parser
import Idris.IDEMode.SyntaxHighlight
import Idris.IDEMode.Pretty

import Protocol.Hex
import Libraries.Utils.Path

import Data.List
import Data.String
import System
import System.File

import Network.Socket
import Network.Socket.Data
import Network.Socket.Raw

import TTImp.Interactive.Completion

import Libraries.Data.String.Extra -- until 0.6.0 release

%default covering

||| TODO: use the version in `Network.FFI` in network after the next release.
%foreign "C:idrnet_fdopen, libidris2_support, idris_net.h"
prim__idrnet_fdopen : Int -> String -> PrimIO AnyPtr

export
socketToFile : Socket -> IO (Either String File)
socketToFile (MkSocket f _ _ _) = do
  file <- FHandle <$> primIO (prim__idrnet_fdopen f "r+")
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
                 do p <- getSockPort sock
                    putStrLn (show p)
                    fflush stdout
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
getInput : File -> IO (Maybe String, String)
getInput f
    = do x <- getNChars f 6
         case fromHexChars (reverse x) of
              Nothing =>
                do rest <- getFLine f
                   pure (Nothing, pack x ++ rest)
              Just num =>
                do inp <- getNChars f (integerToNat num)
                   pure (Just (pack x), pack inp)

||| Do nothing and tell the user to wait for us to implmement this (or join the effort!)
todoCmd : {auto c : Ref Ctxt Defs} ->
          {auto o : Ref ROpts REPLOpts} ->
          String -> Core ()
todoCmd cmdName = iputStrLn $ reflow $ cmdName ++ ": command not yet implemented. Hopefully soon!"


data IDEResult
  = REPL REPLResult
  | CompletionList (List String) String
  | NameList (List Name)
  | FoundHoles (List Holes.Data)
  | Term String   -- should be a PTerm + metadata, or SExp.
  | TTTerm String -- should be a TT Term + metadata, or perhaps SExp
  | NameLocList (List (Name, FC))

replWrap : Core REPLResult -> Core IDEResult
replWrap m = pure $ REPL !m

process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref MD Metadata} ->
          {auto o : Ref ROpts REPLOpts} ->
          IDECommand -> Core IDEResult
process (Interpret cmd)
    = replWrap $ interpret cmd
process (LoadFile fname_in _)
    = do let fname = case !(findIpkg (Just fname_in)) of
                          Nothing => fname_in
                          Just f' => f'
         replWrap $ Idris.REPL.process (Load fname) >>= outputSyntaxHighlighting fname

process (NameAt name Nothing)
    = do defs <- get Ctxt
         glob <- lookupCtxtName (UN (mkUserName name)) (gamma defs)
         let dat = map (\(name, _, gdef) => (name, gdef.location)) glob
         pure (NameLocList dat)
process (NameAt n (Just _))
    = do todoCmd "name-at <name> <line> <column>"
         pure $ REPL $ Edited $ DisplayEdit emptyDoc
process (TypeOf n Nothing)
    = replWrap $ Idris.REPL.process (Check (PRef replFC (UN $ mkUserName n)))
process (TypeOf n (Just (l, c)))
    = replWrap $ Idris.REPL.process
               $ Editing (TypeAt (fromInteger l) (fromInteger c) (UN $ mkUserName n))
process (CaseSplit l c n)
    = replWrap $ Idris.REPL.process
    $ Editing $ CaseSplit False (fromInteger l) (fromInteger c)
    $ UN $ mkUserName n
process (AddClause l n)
    = replWrap $ Idris.REPL.process
    $ Editing $ AddClause False (fromInteger l)
    $ UN $ mkUserName n
process (AddMissing l n)
    = do todoCmd "add-missing"
         pure $ REPL $ Edited $ DisplayEdit emptyDoc
process (Intro l h) =
   do replWrap $ Idris.REPL.process
               $ Editing
               $ Intro False (fromInteger l) (UN $ Basic h) {- hole name -}
process (Refine l h expr) =
   do let Right (_, _, e) = runParser (Virtual Interactive) Nothing expr aPTerm
        | Left err => pure $ REPL $ REPLError (pretty0 $ show err)
      replWrap $ Idris.REPL.process
               $ Editing
               $ Refine False (fromInteger l) (UN $ Basic h) {- hole name -} e
process (ExprSearch l n hs all)
    = replWrap $ Idris.REPL.process (Editing (ExprSearch False (fromInteger l)
                     (UN $ Basic n) (map (UN . Basic) hs.list)))
process ExprSearchNext
    = replWrap $ Idris.REPL.process (Editing ExprSearchNext)
process (GenerateDef l n)
    = replWrap $ Idris.REPL.process (Editing (GenerateDef False (fromInteger l) (UN $ Basic n) 0))
process GenerateDefNext
    = replWrap $ Idris.REPL.process (Editing GenerateDefNext)
process (MakeLemma l n)
    = replWrap $ Idris.REPL.process (Editing (MakeLemma False (fromInteger l) (UN $ mkUserName n)))
process (MakeCase l n)
    = replWrap $ Idris.REPL.process (Editing (MakeCase False (fromInteger l) (UN $ mkUserName n)))
process (MakeWith l n)
    = replWrap $ Idris.REPL.process (Editing (MakeWith False (fromInteger l) (UN $ mkUserName n)))
process (DocsFor n modeOpt)
    = replWrap $ Idris.REPL.process (Doc $ APTerm (PRef EmptyFC (UN $ mkUserName n)))
process (Apropos n)
    = do todoCmd "apropros"
         pure $ REPL $ Printed emptyDoc
process (Directive n)
    = do todoCmd "directive"
         pure $ REPL $ Printed emptyDoc
process (WhoCalls n)
    = do todoCmd "who-calls"
         pure $ NameList []
process (CallsWho n)
    = do todoCmd "calls-who"
         pure $ NameList []
process (BrowseNamespace ns)
    = replWrap $ Idris.REPL.process (Browse (mkNamespace ns))
process (NormaliseTerm tm)
    = do todoCmd "normalise-term"
         pure $ Term tm
process (ShowTermImplicits tm)
    = do todoCmd "show-term-implicits"
         pure $ Term tm
process (HideTermImplicits tm)
    = do todoCmd "hide-term-implicits"
         pure $ Term tm
process (ElaborateTerm tm)
    = do todoCmd "elaborate-term"
         pure $ TTTerm tm
process (PrintDefinition n)
    = do todoCmd "print-definition"
         pure $ REPL $ Printed (pretty0 n)
process (ReplCompletions line)
    = do Just (ctxt, compl) <- completion line
           | Nothing => pure (REPL $ REPLError $ vcat [ "I can't make sense of the completion task:", pretty0 line])
         pure (CompletionList compl ctxt)
process (EnableSyntax b)
    = do setSynHighlightOn b
         pure $ REPL $ Printed (reflow "Syntax highlight option changed to" <++> byShow b)
process Version
    = replWrap $ Idris.REPL.process ShowVersion
process (Metavariables _)
    = FoundHoles <$> getUserHolesData
process GetOptions
    = replWrap $ Idris.REPL.process GetOpts

processCatch : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref MD Metadata} ->
               {auto o : Ref ROpts REPLOpts} ->
               IDECommand -> Core IDEResult
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
                           pure $ REPL $ REPLError msg)

idePutStrLn : {auto c : Ref Ctxt Defs} -> File -> Integer -> String -> Core ()
idePutStrLn outf i msg
    = send outf $ WriteString msg i

returnFromIDE : {auto c : Ref Ctxt Defs} -> File -> Integer -> IDE.ReplyPayload -> Core ()
returnFromIDE outf i payload
    = do send outf (Immediate payload i)

printIDEResult : {auto c : Ref Ctxt Defs} -> File -> Integer -> IDE.Result -> Core ()
printIDEResult outf i result
  = returnFromIDE outf i $ OK result []

printIDEResultWithHighlight :
  {auto c : Ref Ctxt Defs} ->
  File -> Integer -> (Result, List (Span Properties)) ->
  Core ()
printIDEResultWithHighlight outf i (result, spans) = do
--  log "ide-mode.highlight" 10 $ show spans
  returnFromIDE outf i
    $ OK result spans

-- TODO: refactor to construct an error response
printIDEError : Ref ROpts REPLOpts => {auto c : Ref Ctxt Defs} -> File -> Integer -> Doc IdrisAnn -> Core ()
printIDEError outf i msg = returnFromIDE outf i $
  uncurry IDE.Error !(renderWithDecorations annToProperties msg)

Cast REPLEval String where
  cast EvalTC = "typecheck"
  cast NormaliseAll = "normalise"
  cast Execute = "execute"
  cast Scheme = "scheme"

Cast REPLOpt REPLOption where
  cast (ShowImplicits impl)  = MkOption "show-implicits" BOOL impl
  cast (ShowNamespace ns)    = MkOption "show-namespace" BOOL ns
  cast (ShowMachineNames ns) = MkOption "show-machinenames" BOOL ns
  cast (ShowTypes typs)      = MkOption "show-types"     BOOL typs
  cast (EvalMode mod)        = MkOption "eval"           ATOM $ cast mod
  cast (Editor editor)       = MkOption "editor"         STRING editor
  cast (CG str)              = MkOption "cg"             STRING str
  cast (Profile p)           = MkOption "profile"        BOOL p
  cast (EvalTiming p)        = MkOption "evaltiming"     BOOL p


displayIDEResult : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST UState} ->
       {auto s : Ref Syn SyntaxInfo} ->
       {auto m : Ref MD Metadata} ->
       {auto o : Ref ROpts REPLOpts} ->
       File -> Integer -> IDEResult -> Core ()
displayIDEResult outf i  (REPL $ REPLError err)
  = printIDEError outf i err
displayIDEResult outf i  (REPL RequestedHelp  )
  = printIDEResult outf i $ AString displayHelp
displayIDEResult outf i  (REPL $ RequestedDetails details)
  = printIDEResult outf i $ AString details
displayIDEResult outf i  (REPL $ Evaluated x Nothing)
  = printIDEResultWithHighlight outf i
  $ mapFst AString
   !(renderWithDecorations syntaxToProperties $ pretty x)
displayIDEResult outf i  (REPL $ Evaluated x (Just y))
  = printIDEResultWithHighlight outf i
  $ mapFst AString
   !(renderWithDecorations syntaxToProperties
     $ pretty x <++> ":" <++> pretty y)
displayIDEResult outf i  (REPL $ Printed xs)
  = printIDEResultWithHighlight outf i
  $ mapFst AString
  $ !(renderWithDecorations annToProperties xs)
displayIDEResult outf i (REPL (PrintedDoc xs))
  = printIDEResultWithHighlight outf i
  $ mapFst AString
  $ !(renderWithDecorations docToProperties xs)
displayIDEResult outf i  (REPL $ TermChecked x y)
  = printIDEResultWithHighlight outf i
  $ mapFst AString
   !(renderWithDecorations syntaxToProperties
     $ pretty x <++> ":" <++> pretty y)
displayIDEResult outf i  (REPL $ FileLoaded x)
  = printIDEResult outf i $ AUnit
displayIDEResult outf i  (REPL $ ErrorLoadingFile x err)
  = printIDEError outf i $ reflow "Error loading file" <++> pretty0 x <+> colon <++> pretty0 (show err)
displayIDEResult outf i  (REPL $ ErrorsBuildingFile x errs)
  = printIDEError outf i $ reflow "Error(s) building file" <++> pretty0 x -- messages already displayed while building
displayIDEResult outf i  (REPL $ NoFileLoaded)
  = printIDEError outf i $ reflow "No file can be reloaded"
displayIDEResult outf i  (REPL $ CurrentDirectory dir)
  = printIDEResult outf i $ AString $ "Current working directory is \"\{dir}\""
displayIDEResult outf i  (REPL CompilationFailed)
  = printIDEError outf i $ reflow "Compilation failed"
displayIDEResult outf i  (REPL $ Compiled f)
  = printIDEResult outf i $ AString "File \{f} written"
displayIDEResult outf i  (REPL $ ProofFound x)
  = printIDEResult outf i $ AString $ show x
displayIDEResult outf i  (REPL $ Missed cases)
  = printIDEResult outf i
  $ AString $ showSep "\n"
  $ map handleMissing' cases
displayIDEResult outf i  (REPL $ CheckedTotal xs)
  = printIDEResult outf i
  $ AString $ showSep "\n"
  $ map (\ (fn, tot) => (show fn ++ " is " ++ show tot)) xs
displayIDEResult outf i  (REPL $ LogLevelSet k)
  = printIDEResult outf i
  $ AString $ "Set loglevel to " ++ show k
displayIDEResult outf i  (REPL $ OptionsSet opts)
  = printIDEResult outf i $ AnOptionList $ map cast opts
displayIDEResult outf i  (REPL $ VersionIs x)
  = let (major, minor, patch) = semVer x
    in printIDEResult outf i $ AVersion $ MkIdrisVersion
      {major, minor, patch, tag = versionTag x}
displayIDEResult outf i (REPL $ Edited (DisplayEdit xs))
  = printIDEResultWithHighlight outf i
  $ mapFst AString
   !(renderWithDecorations annToProperties $ xs)
displayIDEResult outf i (REPL $ Edited (EditError x))
  = printIDEError outf i x
displayIDEResult outf i (REPL $ Edited (MadeIntro is))
  = printIDEResult outf i $ AnIntroList is
displayIDEResult outf i (REPL $ Edited (MadeLemma lit name pty pappstr))
  = printIDEResult outf i $ AMetaVarLemma $ MkMetaVarLemma
      { application = pappstr
      , lemma = relit lit $ show name ++ " : " ++ show pty
      }
displayIDEResult outf i (REPL $ Edited (MadeWith lit wapp))
  = printIDEResult outf i
  $ AString $ showSep "\n" (map (relit lit) wapp)
displayIDEResult outf i (REPL $ (Edited (MadeCase lit cstr)))
  = printIDEResult outf i
  $ AString $ showSep "\n" (map (relit lit) cstr)
displayIDEResult outf i (FoundHoles holes)
  = printIDEResult outf i $ AHoleList $ map holeIDE holes
displayIDEResult outf i (CompletionList ns r)
  = printIDEResult outf i $ ACompletionList ns r
displayIDEResult outf i (NameList ns)
  = printIDEResult outf i $ ANameList (map show ns)
displayIDEResult outf i (Term t)
  = printIDEResult outf i $ AString t
displayIDEResult outf i (TTTerm t)
  = printIDEResult outf i $ AString t
displayIDEResult outf i (REPL $ ConsoleWidthSet mn)
  = let width = case mn of
                    Just k  => show k
                    Nothing => "auto"
    in printIDEResult outf i $ AString $ "Set consolewidth to " ++ width
displayIDEResult outf i (NameLocList dat)
  = printIDEResult outf i $ ANameLocList $
       !(traverse (constructFileContext . map toNonEmptyFC) dat)
  where
    -- In order to recover the full path to the module referenced by FC,
    -- which stores a module identifier as opposed to a full path,
    -- we need to check the project's source folder and all the library directories
    -- for the relevant source file.
    -- (!) Always returns the *absolute* path.
    sexpOriginDesc : OriginDesc -> Core String
    sexpOriginDesc (PhysicalIdrSrc modIdent) = do
      defs <- get Ctxt
      let wdir = defs.options.dirs.working_dir
      let pkg_dirs = filter (/= ".") (defs.options.dirs.extra_dirs ++ defs.options.dirs.package_dirs)
      let exts = listOfExtensionsStr
      Just fname <- catch
          (Just . (wdir </>) <$> nsToSource replFC modIdent) -- Try local source first
          -- if not found, try looking for the file amongst the loaded packages.
          (const $ firstAvailable $ do
            pkg_dir <- pkg_dirs
            let pkg_dir_abs = ifThenElse (isRelative pkg_dir) (wdir </> pkg_dir) pkg_dir
            ext <- exts
            pure (pkg_dir_abs </> ModuleIdent.toPath modIdent <.> ext))
        | _ => pure "(File-Not-Found)"
      pure fname
    sexpOriginDesc (PhysicalPkgSrc fname) = pure fname
    sexpOriginDesc (Virtual Interactive) = pure "(Interactive)"

    constructFileContext : (Name, NonEmptyFC) -> Core (String, FileContext)
    constructFileContext (name, origin, (startLine, startCol), (endLine, endCol)) = pure $
        -- TODO: fix the emacs mode to use the more structured SExpr representation
        (!(render $ pretty0 name)
        , MkFileContext
          { file  = !(sexpOriginDesc origin)
          , range = MkBounds {startCol, startLine, endCol, endLine}
          })

-- do not use a catchall so that we are warned about missing cases when adding a
-- new construtor to the enumeration.
displayIDEResult outf i (REPL Done) = printIDEResult outf i (AString "")
displayIDEResult outf i (REPL (Executed _)) = printIDEResult outf i (AString "")
displayIDEResult outf i (REPL (ModuleLoaded _)) = printIDEResult outf i (AString "")
displayIDEResult outf i (REPL (ErrorLoadingModule _ _)) = printIDEResult outf i (AString "")
displayIDEResult outf i (REPL (ColorSet _)) = printIDEResult outf i (AString "")
displayIDEResult outf i (REPL DefDeclared) = printIDEResult outf i (AString "")
displayIDEResult outf i (REPL Exited) = printIDEResult outf i (AString "")


handleIDEResult : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST UState} ->
       {auto s : Ref Syn SyntaxInfo} ->
       {auto m : Ref MD Metadata} ->
       {auto o : Ref ROpts REPLOpts} ->
       File -> Integer -> IDEResult -> Core ()
handleIDEResult outf i (REPL Exited) = idePutStrLn outf i "Bye for now!"
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
              REPL _ => printError $ reflow "Running idemode but output isn't"
              IDEMode idx inf outf => do
                (pref, inp) <- coreLift $ getInput inf
                log "ide-mode.recv" 50 $ "Received: \{fromMaybe "" pref}\{inp}"
                end <- coreLift $ fEOF inf
                unless end $ do
                  case parseSExp inp of
                    Left err =>
                      do printIDEError outf idx (reflow "Parse error:" <++> !(perror err))
                         loop
                    Right sexp =>
                      case getMsg sexp of
                        Just (cmd, i) =>
                          do updateOutput i
                             res <- processCatch cmd
                             handleIDEResult outf i res
                             loop
                        Nothing =>
                          do printIDEError outf idx (reflow "Unrecognised command:" <++> pretty0 (show sexp))
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
              REPL _ => printError $ reflow "Running idemode but output isn't"
              IDEMode _ inf outf => do
                send outf (ProtocolVersion 2 1) -- TODO: Move this info somewhere more central
                loop
