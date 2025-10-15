module Idris.Parser.Repl

import Core.Options
import Core.Metadata
import Idris.Syntax
import Idris.Syntax.Traversals
import public Idris.Parser.Core.Source
import TTImp.TTImp

import public Libraries.Text.Parser
import Data.Either
import Libraries.Data.IMaybe
import Data.List
import Data.List.Quantifiers
import Data.List1
import Data.Maybe
import Data.So
import Data.Nat
import Data.SnocList
import Data.String
import Libraries.Utils.String
import Libraries.Data.WithDefault

import Idris.Parser.Let
import Idris.Parser.Basic
import Idris.Parser.Source
%hide Prelude.(>>)
%hide Prelude.(>>=)
%hide Core.Core.(>>)
%hide Core.Core.(>>=)
%hide Prelude.pure
%hide Core.Core.pure
%hide Prelude.(<*>)
%hide Core.Core.(<*>)

%default covering


parseMode : Rule REPLEval
parseMode
     = do exactIdent "typecheck"
          pure EvalTC
   <|> do exactIdent "tc"
          pure EvalTC
   <|> do exactIdent "normalise"
          pure NormaliseAll
   <|> do exactIdent "default"
          pure NormaliseAll
   <|> do exactIdent "normal"
          pure NormaliseAll
   <|> do exactIdent "normalize" -- oh alright then
          pure NormaliseAll
   <|> do exactIdent "execute"
          pure Execute
   <|> do exactIdent "exec"
          pure Execute
   <|> do exactIdent "scheme"
          pure Scheme

setVarOption : Rule REPLOpt
setVarOption
    = do exactIdent "eval"
         mode <- option NormaliseAll parseMode
         pure (EvalMode mode)
  <|> do exactIdent "editor"
         e <- unqualifiedName
         pure (Editor e)
  <|> do exactIdent "cg"
         c <- unqualifiedName
         pure (CG c)

setOption : Bool -> Rule REPLOpt
setOption set
    = do exactIdent "showimplicits"
         pure (ShowImplicits set)
  <|> do exactIdent "shownamespace"
         pure (ShowNamespace set)
  <|> do exactIdent "showmachinenames"
         pure (ShowMachineNames set)
  <|> do exactIdent "showtypes"
         pure (ShowTypes set)
  <|> do exactIdent "profile"
         pure (Profile set)
  <|> do exactIdent "evaltiming"
         pure (EvalTiming set)
  <|> if set then setVarOption else fatalError "Unrecognised option"

replCmd : List String -> Rule ()
replCmd [] = fail "Unrecognised command"
replCmd (c :: cs)
    = exactIdent c
  <|> symbol c
  <|> replCmd cs

cmdName : String -> Rule String
cmdName str = do
  _ <- optional (symbol ":")
  terminal ("Unrecognised REPL command '" ++ str ++ "'") $
           \case
              (Ident s)       => if s == str then Just s else Nothing
              (Keyword kw)    => if kw == str then Just kw else Nothing
              (Symbol "?")    => Just "?"
              (Symbol ":?")   => Just "?"   -- `:help :?` is a special case
              _ => Nothing

export
data CmdArg : Type where
     ||| The command takes no arguments.
     NoArg : CmdArg

     ||| The command takes a name.
     NameArg : CmdArg

     ||| The command takes an expression.
     ExprArg : CmdArg

     ||| The command takes a documentation directive.
     DocArg : CmdArg

     ||| The command takes a list of declarations
     DeclsArg : CmdArg

     ||| The command takes a number.
     NumberArg : CmdArg

     ||| The command takes a number or auto.
     AutoNumberArg : CmdArg

     ||| The command takes an option.
     OptionArg : CmdArg

     ||| The command takes a file.
     FileArg : CmdArg

     ||| The command takes a module.
     ModuleArg : CmdArg

     ||| The command takes a string
     StringArg : CmdArg

     ||| The command takes a on or off.
     OnOffArg : CmdArg

     ||| The command takes an argument documenting its name
     NamedCmdArg : String -> CmdArg -> CmdArg

     ||| The command takes an argument documenting its default value
     WithDefaultArg : String -> CmdArg -> CmdArg

     ||| The command takes arguments separated by commas
     CSVArg : CmdArg -> CmdArg

     ||| The command takes multiple arguments.
     Args : List CmdArg -> CmdArg

mutual
  covering
  showCmdArg : CmdArg -> String
  showCmdArg NoArg = ""
  showCmdArg NameArg = "name"
  showCmdArg ExprArg = "expr"
  showCmdArg DocArg = "keyword|expr"
  showCmdArg DeclsArg = "decls"
  showCmdArg NumberArg = "number"
  showCmdArg AutoNumberArg = "number|auto"
  showCmdArg OptionArg = "option"
  showCmdArg FileArg = "file"
  showCmdArg ModuleArg = "module"
  showCmdArg StringArg = "string"
  showCmdArg OnOffArg = "(on|off)"
  showCmdArg (CSVArg arg) = "[" ++ showCmdArg arg ++ "]"
  showCmdArg (WithDefaultArg value arg) = showCmdArg arg ++ "|" ++ value
  showCmdArg (NamedCmdArg name arg) = name ++ ":" ++ showCmdArg arg
  showCmdArg args@(Args _) = show args

  export
  covering
  Show CmdArg where
    show NoArg = ""
    show OnOffArg = "(on|off)"
    show (Args args) = showSep " " (map show args)
    show arg = "<" ++ showCmdArg arg ++ ">"

public export
knownCommands : List (String, String)
knownCommands =
  explain ["t", "type"] "Check the type of an expression" ++
  [ ("ti", "Check the type of an expression, showing implicit arguments")
  , ("printdef", "Show the definition of a pattern-matching function")
  ] ++
  explain ["s", "search"] "Search for values by type" ++
  [ ("di", "Show debugging information for a name")
  ] ++
  explain ["module", "import"] "Import an extra module" ++
  [ ("package", "Import every module of the package")
  ] ++
  explain ["q", "quit", "exit"] "Exit the Idris system" ++
  [ ("cwd", "Displays the current working directory")
  , ("cd", "Change the current working directory")
  , ("sh", "Run a shell command")
  , ("set"
    , unlines   -- FIXME: this should be a multiline string (see #2087)
      [ "Set an option"
      , "  eval                specify what evaluation mode to use:"
      , "                        typecheck|tc"
      , "                        normalise|normalize|normal"
      , "                        execute|exec"
      , "                        scheme"
      , ""
      , "  editor              specify the name of the editor command"
      , ""
      , "  cg                  specify the codegen/backend to use"
      , "                      builtin codegens are:"
      , "                        chez"
      , "                        racket"
      , "                        refc"
      , "                        node"
      , ""
      , "  showimplicits       enable displaying implicit arguments as part of the"
      , "                      output"
      , ""
      , "  shownamespace       enable displaying namespaces as part of the output"
      , ""
      , "  showmachinenames    enable displaying machine names as part of the"
      , "                      output"
      , ""
      , "  showtypes           enable displaying the type of the term as part of"
      , "                      the output"
      , ""
      , "  profile"
      , ""
      , "  evaltiming          enable timing how long evaluation takes and"
      , "                      displaying this before the printing of the output"
      ]
    )
  , ("unset", "Unset an option")
  , ("opts", "Show current options settings")
  ] ++
  explain ["c", "compile"] "Compile to an executable" ++
  [ ("exec", "Compile to an executable and run")
  , ("directive", "Set a codegen-specific directive")
  ] ++
  explain ["l", "load"] "Load a file" ++
  explain ["r", "reload"] "Reload current file" ++
  explain ["e", "edit"] "Edit current file using $EDITOR or $VISUAL" ++
  explain ["miss", "missing"] "Show missing clauses" ++
  [ ("total", "Check the totality of a name")
  , ("doc", "Show documentation for a keyword, a name, or a primitive")
  , ("browse", "Browse contents of a namespace")
  ] ++
  explain ["log", "logging"] "Set logging level" ++
  [ ("consolewidth", "Set the width of the console output (0 for unbounded) (auto by default)")
  ] ++
  explain ["colour", "color"] "Whether to use colour for the console output (enabled by default)" ++
  explain ["m", "metavars"] "Show remaining proof obligations (metavariables or holes)" ++
  [ ("typeat", "Show type of term <n> defined on line <l> and column <c>")
  ] ++
  explain ["cs", "casesplit"] "Case split term <n> defined on line <l> and column <c>" ++
  explain ["ac", "addclause"] "Add clause to term <n> defined on line <l>" ++
  explain ["ml", "makelemma"] "Make lemma for term <n> defined on line <l>" ++
  explain ["mc", "makecase"] "Make case on term <n> defined on line <l>" ++
  explain ["mw", "makewith"] "Add with expression on term <n> defined on line <l>" ++
  [ ("intro", "Introduce unambiguous constructor in hole <n> defined on line <l>")
  , ("refine", "Refine hole <h> with identifier <n> on line <l>")
  ] ++
  explain ["ps", "proofsearch"] "Search for a proof" ++
  [ ("psnext", "Show next proof")
  , ("gd", "Try to generate a definition using proof-search")
  , ("gdnext", "Show next definition")
  , ("version", "Display the Idris version")
  ] ++
  explain ["?", "h", "help"] (unlines     -- FIXME: this should be a multiline string (see #2087)
        [ "Display help text, optionally of a specific command.\n"
        , "If run without arguments, lists all the REPL commands along with their"
        , "initial line of help text.\n"
        , "More detailed help can then be obtained by running the :help command"
        , "with another command as an argument, e.g."
        , "  > :help :help"
        , "  > :help :set"
        , "(the leading ':' in the command argument is optional)"
        ] ) ++
  [ ( "let"
    , """
      Define a new value.

      First, declare the type of your new value, e.g.
        :let myValue : List Nat

      Then, define the value:
        :let myValue = [1, 2, 3]

      Now the value is in scope at the REPL:
        > map (+ 2) myValue
        [3, 4, 5]
      """
    )
  ] ++
  explain ["fs", "fsearch"] """
    Search for global definitions by sketching the names distribution of the wanted type(s).

    The parameter must be in one of the forms A -> B, A -> _, or B, where A and B are space-delimited lists of global names.

    Idris will return all of the entries in the context that have all of the names in A
    in some argument and all of the names in B within the return type.

    For example:

      :fs List Maybe -> List

    will match (among other things):

      Prelude.List.mapMaybe : (a -> Maybe b) -> List a -> List b

    Note that the query 'List Nat -> String' does not describe the type 'List Nat',
    rather it describes both 'List a' and 'Nat' in the arguments.

    """
  where
    explain : List String -> String -> List (String, String)
    explain cmds expl = map (\s => (s, expl)) cmds

public export
KnownCommand : String -> Type
KnownCommand cmd = IsJust (lookup cmd knownCommands)

export
data ParseCmd : Type where
     ParseREPLCmd :  (cmds : List String)
                  -> {auto 0 _ : All KnownCommand cmds}
                  -> ParseCmd

     ParseKeywordCmd :  (cmds : List String)
                     -> {auto 0 _ : All KnownCommand cmds}
                     -> ParseCmd

     ParseIdentCmd :  (cmd : String)
                   -> {auto 0 _ : KnownCommand cmd}
                   -> ParseCmd

public export
CommandDefinition : Type
CommandDefinition = (List String, CmdArg, String, Rule REPLCmd)

public export
CommandTable : Type
CommandTable = List CommandDefinition

extractNames : ParseCmd -> List String
extractNames (ParseREPLCmd names) = names
extractNames (ParseKeywordCmd keywords) = keywords
extractNames (ParseIdentCmd ident) = [ident]

runParseCmd : ParseCmd -> Rule ()
runParseCmd (ParseREPLCmd names) = replCmd names
runParseCmd (ParseKeywordCmd keywords) = choice $ map keyword keywords
runParseCmd (ParseIdentCmd ident) = exactIdent ident


noArgCmd : ParseCmd -> REPLCmd -> String -> CommandDefinition
noArgCmd parseCmd command doc = (names, NoArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      pure command

nameArgCmd : ParseCmd -> (Name -> REPLCmd) -> String -> CommandDefinition
nameArgCmd parseCmd command doc = (names, NameArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      n <- mustWork name
      pure (command n)

stringArgCmd : ParseCmd -> (String -> REPLCmd) -> String -> CommandDefinition
stringArgCmd parseCmd command doc = (names, StringArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      s <- mustWork simpleStr
      pure (command s)

getHelpType : EmptyRule HelpType
getHelpType = do
  optCmd <- optional $ choice $ (cmdName . fst) <$> knownCommands
  pure $
    case optCmd of
         Nothing => GenericHelp
         Just cmd => DetailedHelp $ fromMaybe "Unrecognised command '\{cmd}'"
                                  $ lookup cmd knownCommands

helpCmd :  ParseCmd
        -> (HelpType -> REPLCmd)
        -> String
        -> CommandDefinition
helpCmd parseCmd command doc = (names, StringArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      helpType <- getHelpType
      pure (command helpType)

moduleArgCmd : ParseCmd -> (ModuleIdent -> REPLCmd) -> String -> CommandDefinition
moduleArgCmd parseCmd command doc = (names, ModuleArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      n <- mustWork moduleIdent
      pure (command n)

exprArgCmd : ParseCmd -> (PTerm -> REPLCmd) -> String -> CommandDefinition
exprArgCmd parseCmd command doc = (names, ExprArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      tm <- mustWork $ typeExpr pdef (Virtual Interactive) init
      pure (command tm)

docArgCmd : ParseCmd -> (DocDirective -> REPLCmd) -> String -> CommandDefinition
docArgCmd parseCmd command doc = (names, DocArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    -- by default, lazy primitives must be followed by a simpleExpr, so we have
    -- this custom parser for the doc case
    docLazyPrim : Rule PTerm
    docLazyPrim =
      let placeholeder : PTerm' Name
          placeholeder = PHole EmptyFC False "lazyDocPlaceholeder"
      in  do exactIdent "Lazy"    -- v
             pure (PDelayed EmptyFC LLazy placeholeder)
      <|> do exactIdent "Inf"     -- v
             pure (PDelayed EmptyFC LInf placeholeder)
      <|> do exactIdent "Delay"
             pure (PDelay EmptyFC placeholeder)
      <|> do exactIdent "Force"
             pure (PForce EmptyFC placeholeder)

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      dir <- mustWork $
        AModule <$ keyword "module" <*> moduleIdent -- must be before Keyword to not be captured
        <|> Keyword <$> anyKeyword
        <|> Symbol <$> (anyReservedSymbol <* eoi
                       <|> parens (Virtual Interactive) anyReservedSymbol <* eoi)
        <|> Bracket <$> (
              IdiomBrackets <$ symbol "[|" <* symbol "|]"
              <|> NameQuote <$ symbol "`{" <* symbol "}"
              <|> TermQuote <$ symbol "`(" <* symbol ")"
              <|> DeclQuote <$ symbol "`[" <* symbol "]"
              )
        <|> APTerm <$> (
              docLazyPrim
              <|> typeExpr pdef (Virtual Interactive) init
              )
      pure (command dir)

declsArgCmd : ParseCmd -> (List PDecl -> REPLCmd) -> String -> CommandDefinition
declsArgCmd parseCmd command doc = (names, DeclsArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd
    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      tm <- mustWork $ topDecl (Virtual Interactive) init
      pure (command [tm])

optArgCmd : ParseCmd -> (REPLOpt -> REPLCmd) -> Bool -> String -> CommandDefinition
optArgCmd parseCmd command set doc = (names, OptionArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      opt <- mustWork $ setOption set
      pure (command opt)

numberArgCmd : ParseCmd -> (Nat -> REPLCmd) -> String -> CommandDefinition
numberArgCmd parseCmd command doc = (names, NumberArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      i <- mustWork intLit
      pure (command (fromInteger i))

autoNumberArgCmd : ParseCmd -> (Maybe Nat -> REPLCmd) -> String -> CommandDefinition
autoNumberArgCmd parseCmd command doc = (names, AutoNumberArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    autoNumber : Rule (Maybe Nat)
    autoNumber = Nothing <$ keyword "auto"
             <|> Just . fromInteger <$> intLit

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      mi <- mustWork autoNumber
      pure (command mi)

onOffArgCmd : ParseCmd -> (Bool -> REPLCmd) -> String -> CommandDefinition
onOffArgCmd parseCmd command doc = (names, OnOffArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      i <- mustWork onOffLit
      pure (command i)

compileArgsCmd : ParseCmd -> (PTerm -> String -> REPLCmd) -> String -> CommandDefinition
compileArgsCmd parseCmd command doc
    = (names, Args [FileArg, ExprArg], doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      n <- mustWork unqualifiedName
      tm <- mustWork $ expr pdef (Virtual Interactive) init
      pure (command tm n)

loggingArgCmd : ParseCmd -> (Maybe LogLevel -> REPLCmd) -> String -> CommandDefinition
loggingArgCmd parseCmd command doc = (names, Args [StringArg, NumberArg], doc, parse) where

  names : List String
  names = extractNames parseCmd

  parse : Rule REPLCmd
  parse = do
    symbol ":"
    runParseCmd parseCmd
    lvl <- mustWork $ Source.logLevel (Virtual Interactive)
    pure (command lvl)

editLineNameArgCmd : ParseCmd -> (Bool -> Int -> Name -> EditCmd) -> String -> CommandDefinition
editLineNameArgCmd parseCmd command doc = (names, Args [NamedCmdArg "l" NumberArg, NamedCmdArg "n" StringArg], doc, parse) where

  names : List String
  names = extractNames parseCmd

  parse : Rule REPLCmd
  parse = do
    symbol ":"
    runParseCmd parseCmd
    upd <- option False (symbol "!" $> True)
    line <- fromInteger <$> mustWork intLit
    n <- mustWork name
    pure (Editing $ command upd line n)

editLineColNameArgCmd : ParseCmd -> (Bool -> Int -> Int -> Name -> EditCmd) -> String -> CommandDefinition
editLineColNameArgCmd parseCmd command doc =
  ( names
  , Args [ NamedCmdArg "l" NumberArg
         , NamedCmdArg "c" NumberArg
         , NamedCmdArg "n" StringArg
         ]
  , doc
  , parse
  ) where

  names : List String
  names = extractNames parseCmd

  parse : Rule REPLCmd
  parse = do
    symbol ":"
    runParseCmd parseCmd
    upd <- option False (symbol "!" $> True)
    line <- fromInteger <$> mustWork intLit
    col <- fromInteger <$> mustWork intLit
    n <- mustWork name
    pure (Editing $ command upd line col n)

editLineNamePTermArgCmd : ParseCmd -> (Bool -> Int -> Name -> PTerm -> EditCmd) -> String -> CommandDefinition
editLineNamePTermArgCmd parseCmd command doc =
  ( names
  , Args [ NamedCmdArg "l" NumberArg
         , NamedCmdArg "h" StringArg
         , NamedCmdArg "e" ExprArg
         ]
  , doc
  , parse
  ) where

  names : List String
  names = extractNames parseCmd

  parse : Rule REPLCmd
  parse = do
    symbol ":"
    runParseCmd parseCmd
    upd <- option False (symbol "!" $> True)
    line <- fromInteger <$> mustWork intLit
    h <- mustWork name
    n <- mustWork $ typeExpr pdef (Virtual Interactive) init
    pure (Editing $ command upd line h n)

editLineNameCSVArgCmd : ParseCmd
                       -> (Bool -> Int -> Name -> List Name -> EditCmd)
                       -> String
                       -> CommandDefinition
editLineNameCSVArgCmd parseCmd command doc =
  ( names
  , Args [ NamedCmdArg "l" NumberArg
         , NamedCmdArg "n" StringArg
         , NamedCmdArg "h" (CSVArg NameArg)
         ]
  , doc
  , parse
  ) where

  names : List String
  names = extractNames parseCmd

  parse : Rule REPLCmd
  parse = do
    symbol ":"
    runParseCmd parseCmd
    upd <- option False (symbol "!" $> True)
    line <- fromInteger <$> mustWork intLit
    n <- mustWork name
    hints <- mustWork $ sepBy (symbol ",") name
    pure (Editing $ command upd line n hints)

editLineNameOptionArgCmd : ParseCmd
                        -> (Bool -> Int -> Name -> Nat -> EditCmd)
                        -> String
                        -> CommandDefinition
editLineNameOptionArgCmd parseCmd command doc =
  ( names
  , Args [ NamedCmdArg "l" NumberArg
         , NamedCmdArg "n" StringArg
         , NamedCmdArg "r" (WithDefaultArg "0" NumberArg)
         ]
  , doc
  , parse
  ) where

  names : List String
  names = extractNames parseCmd

  parse : Rule REPLCmd
  parse = do
    symbol ":"
    runParseCmd parseCmd
    upd <- option False (symbol "!" $> True)
    line <- fromInteger <$> mustWork intLit
    n <- mustWork name
    nreject <- fromInteger <$> option 0 intLit
    pure (Editing $ command upd line n nreject)

firstHelpLine : (cmd : String) -> {auto 0 _ : KnownCommand cmd} -> String
firstHelpLine cmd =
  head . (split ((==) '\n')) $
  fromMaybe "Failed to look up '\{cmd}' (SHOULDN'T HAPPEN!)" $
  lookup cmd knownCommands

export
parserCommandsForHelp : CommandTable
parserCommandsForHelp =
  [ exprArgCmd (ParseREPLCmd ["t", "type"]) Check (firstHelpLine "t")
  , exprArgCmd (ParseREPLCmd ["ti"]) CheckWithImplicits (firstHelpLine "ti")
  , exprArgCmd (ParseREPLCmd ["printdef"]) PrintDef (firstHelpLine "printdef")
  , exprArgCmd (ParseREPLCmd ["s", "search"]) TypeSearch (firstHelpLine "s")
  , nameArgCmd (ParseIdentCmd "di") DebugInfo (firstHelpLine "di")
  , moduleArgCmd (ParseKeywordCmd ["module", "import"]) ImportMod (firstHelpLine "module")
  , stringArgCmd (ParseREPLCmd ["package"]) ImportPackage (firstHelpLine "package")
  , noArgCmd (ParseREPLCmd ["q", "quit", "exit"]) Quit (firstHelpLine "q")
  , noArgCmd (ParseREPLCmd ["cwd"]) CWD (firstHelpLine "cwd")
  , stringArgCmd (ParseREPLCmd ["cd"]) CD (firstHelpLine "cd")
  , stringArgCmd (ParseREPLCmd ["sh"]) RunShellCommand (firstHelpLine "sh")
  , optArgCmd (ParseIdentCmd "set") SetOpt True (firstHelpLine "set")
  , optArgCmd (ParseIdentCmd "unset") SetOpt False (firstHelpLine "unset")
  , noArgCmd (ParseREPLCmd ["opts"]) GetOpts (firstHelpLine "opts")
  , compileArgsCmd (ParseREPLCmd ["c", "compile"]) Compile (firstHelpLine "c")
  , exprArgCmd (ParseIdentCmd "exec") Exec (firstHelpLine "exec")
  , stringArgCmd (ParseIdentCmd "directive") CGDirective (firstHelpLine "directive")
  , stringArgCmd (ParseREPLCmd ["l", "load"]) Load (firstHelpLine "l")
  , noArgCmd (ParseREPLCmd ["r", "reload"]) Reload (firstHelpLine "r")
  , noArgCmd (ParseREPLCmd ["e", "edit"]) Edit (firstHelpLine "e")
  , nameArgCmd (ParseREPLCmd ["miss", "missing"]) Missing (firstHelpLine "miss")
  , nameArgCmd (ParseKeywordCmd ["total"]) Total (firstHelpLine "total")
  , docArgCmd (ParseIdentCmd "doc") Doc (firstHelpLine "doc")
  , moduleArgCmd (ParseIdentCmd "browse") (Browse . miAsNamespace) (firstHelpLine "browse")
  , loggingArgCmd (ParseREPLCmd ["log", "logging"]) SetLog (firstHelpLine "log")
  , autoNumberArgCmd (ParseREPLCmd ["consolewidth"]) SetConsoleWidth (firstHelpLine "consolewidth")
  , onOffArgCmd (ParseREPLCmd ["colour", "color"]) SetColor (firstHelpLine "colour")
  , noArgCmd (ParseREPLCmd ["m", "metavars"]) Metavars (firstHelpLine "m")
  , editLineColNameArgCmd (ParseREPLCmd ["typeat"]) (const TypeAt) (firstHelpLine "typeat")
  , editLineColNameArgCmd (ParseREPLCmd ["cs", "casesplit"]) CaseSplit (firstHelpLine "cs")
  , editLineNameArgCmd (ParseREPLCmd ["ac", "addclause"]) AddClause (firstHelpLine "ac")
  , editLineNameArgCmd (ParseREPLCmd ["ml", "makelemma"]) MakeLemma (firstHelpLine "ml")
  , editLineNameArgCmd (ParseREPLCmd ["mc", "makecase"]) MakeCase (firstHelpLine "mc")
  , editLineNameArgCmd (ParseREPLCmd ["mw", "makewith"]) MakeWith (firstHelpLine "mw")
  , editLineNameArgCmd (ParseREPLCmd ["intro"]) Intro (firstHelpLine "intro")
  , editLineNamePTermArgCmd (ParseREPLCmd ["refine"]) Refine (firstHelpLine "refine")
  , editLineNameCSVArgCmd (ParseREPLCmd ["ps", "proofsearch"]) ExprSearch (firstHelpLine "ps")
  , noArgCmd (ParseREPLCmd ["psnext"]) (Editing ExprSearchNext) (firstHelpLine "psnext")
  , editLineNameOptionArgCmd (ParseREPLCmd ["gd"]) GenerateDef (firstHelpLine "gd")
  , noArgCmd (ParseREPLCmd ["gdnext"]) (Editing GenerateDefNext) (firstHelpLine "gdnext")
  , noArgCmd (ParseREPLCmd ["version"]) ShowVersion (firstHelpLine "version")
  , helpCmd (ParseREPLCmd ["?", "h", "help"]) Help (firstHelpLine "?")
  , declsArgCmd (ParseKeywordCmd ["let"]) NewDefn (firstHelpLine "let")
  , exprArgCmd (ParseREPLCmd ["fs", "fsearch"]) FuzzyTypeSearch (firstHelpLine "fs")
  ]

export
help : List (List String, CmdArg, String)
help = (["<expr>"], NoArg, "Evaluate an expression") ::
         map (\ (names, args, text, _) =>
               (map (":" ++) names, args, text)) parserCommandsForHelp

nonEmptyCommand : Rule REPLCmd
nonEmptyCommand =
  choice (map (\ (_, _, _, parser) => parser) parserCommandsForHelp)

eval : Rule REPLCmd
eval = do
  tm <- typeExpr pdef (Virtual Interactive) init
  pure (Eval tm)

export
aPTerm : Rule PTerm
aPTerm = typeExpr pdef (Virtual Interactive) init

export
command : EmptyRule REPLCmd
command
    = eoi $> NOP
  <|> nonEmptyCommand
  <|> (do symbol ":?" -- special case, :? doesn't fit into above scheme
          helpType <- getHelpType
          pure $ Help helpType)
  <|> eval
