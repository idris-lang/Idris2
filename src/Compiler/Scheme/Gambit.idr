module Compiler.Scheme.Gambit

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Generated
import Compiler.Opts.ToplevelConstants
import Compiler.Scheme.Common

import Core.Context
import Core.Directory
import Core.Name
import Core.Options
import Core.TT
import Protocol.Hex
import Libraries.Utils.Path
import Libraries.Data.SortedSet
import Libraries.Data.String.Builder

import Data.List
import Data.Maybe
import Data.Vect

import Idris.Env
import Idris.Syntax

import System
import System.Directory

%default covering

-- TODO Look for gsi-script, then gsi
findGSI : IO (List String)
findGSI =
  do env <- idrisGetEnv "GAMBIT_GSI"
     pure $ maybe ["/usr/bin/env", "gsi"] singleton env

-- TODO Look for gsc-script, then gsc
findGSC : IO (List String)
findGSC =
  do env <- idrisGetEnv "GAMBIT_GSC"
     pure $ maybe ["/usr/bin/env", "gsc"] singleton env

findGSCBackend : IO (List String)
findGSCBackend =
  do env <- idrisGetEnv "GAMBIT_GSC_BACKEND"
     pure $ case env of
              Nothing => []
              Just e => ["-cc", e]

schHeader : Builder
schHeader = fromString """
  ;; \{ generatedString "Gambit" }
  (declare (block)
    (inlining-limit 450)
    (standard-bindings)
    (extended-bindings)
    (not safe)
    (optimize-dead-definitions))

  """

showGambitChar : Char -> Builder -> Builder
showGambitChar '\\' acc = "\\\\" ++ acc
showGambitChar c acc
   = if ord c < 32 -- XXX
        then fromString ("\\x" ++ fromString (asHex (cast c)) ++ ";") ++ acc
        else char c ++ acc

showGambitString : List Char -> Builder -> Builder
showGambitString [] acc = acc
showGambitString ('"' :: cs) acc = "\\\"" ++ showGambitString cs acc
showGambitString (c :: cs) acc = showGambitChar c $ showGambitString cs acc

gambitString : String -> Builder
gambitString cs = "\"" ++ showGambitString (unpack cs) "\""

handleRet : CFType -> Builder -> Builder
handleRet CFUnit op = op ++ " " ++ mkWorld (schConstructor gambitString (UN $ Basic "") (Just 0) [])
handleRet _ op = mkWorld op

getFArgs : NamedCExp -> Core (List (NamedCExp, NamedCExp))
getFArgs (NmCon fc _ _ (Just 0) _) = pure []
getFArgs (NmCon fc _ _ (Just 1) [ty, val, rest]) = pure $ (ty, val) :: !(getFArgs rest)
getFArgs arg = throw (GenericMsg (getFC arg) ("Badly formed c call argument list " ++ show arg))

gambitPrim : SortedSet Name -> LazyExprProc -> Nat -> ExtPrim -> List NamedCExp -> Core Builder
gambitPrim cs schLazy i GetField [NmPrimVal _ (Str s), _, _, struct,
                       NmPrimVal _ (Str fld), _]
    = do structsc <- schExp cs (gambitPrim cs schLazy) gambitString schLazy 0 struct
         pure $ "(" ++ fromString s ++ "-" ++ fromString fld ++ " " ++ structsc ++ ")"
gambitPrim cs schLazy i GetField [_,_,_,_,_,_]
    = pure "(error \"bad getField\")"
gambitPrim cs schLazy i SetField [NmPrimVal _ (Str s), _, _, struct,
                       NmPrimVal _ (Str fld), _, val, world]
    = do structsc <- schExp cs (gambitPrim cs schLazy) gambitString schLazy 0 struct
         valsc <- schExp cs (gambitPrim cs schLazy) gambitString schLazy 0 val
         pure $ mkWorld $
              "(" ++ fromString s ++ "-" ++ fromString fld ++ "-set! " ++ structsc ++ " " ++ valsc ++ ")"
gambitPrim cs schLazy i SetField [_,_,_,_,_,_,_,_]
    = pure "(error \"bad setField\")"
gambitPrim cs schLazy i SysCodegen []
    = pure $ "\"gambit\""
gambitPrim cs schLazy i prim args
    = schExtCommon cs (gambitPrim cs schLazy) gambitString schLazy i prim args

-- Reference label for keeping track of loaded external libraries
data Loaded : Type where

-- Label for noting which struct types are declared
data Structs : Type where

notWorld : CFType -> Bool
notWorld CFWorld = False
notWorld _ = True

cType : FC -> CFType -> Core Builder
cType fc CFUnit = pure "void"
cType fc CFInt = pure "int"
cType fc CFString = pure "char *"
cType fc CFDouble = pure "double"
cType fc CFChar = pure "char"
cType fc CFPtr = pure "void *"
cType fc (CFIORes t) = cType fc t
cType fc (CFStruct n t) = pure $ "struct " ++ fromString n
cType fc (CFFun s t) = funTySpec [s] t
  where
    funTySpec : List CFType -> CFType -> Core Builder
    funTySpec args (CFFun CFWorld t) = funTySpec args t
    funTySpec args (CFFun s t) = funTySpec (s :: args) t
    funTySpec args retty
        = do rtyspec <- cType fc retty
             argspecs <- traverse (cType fc) (reverse . filter notWorld $ args)
             pure $ rtyspec ++ " (*)(" ++ sepBy ", " argspecs ++ ")"
cType fc t = throw (GenericMsg fc ("Can't pass argument of type " ++ show t ++
                       " to foreign function"))

cftySpec : FC -> CFType -> Core Builder
cftySpec fc CFUnit = pure "void"
cftySpec fc CFInt = pure "int"
cftySpec fc CFInt8 = pure "char"
cftySpec fc CFInt16 = pure "short"
cftySpec fc CFInt32 = pure "int"
cftySpec fc CFInt64 = pure "long"
cftySpec fc CFUnsigned8 = pure "unsigned-char"
cftySpec fc CFUnsigned16 = pure "unsigned-short"
cftySpec fc CFUnsigned32 = pure "unsigned-int"
cftySpec fc CFUnsigned64 = pure "unsigned-long"
cftySpec fc CFString = pure "UTF-8-string"
cftySpec fc CFDouble = pure "double"
cftySpec fc CFChar = pure "char"
cftySpec fc CFPtr = pure "(pointer void)"
cftySpec fc (CFIORes t) = cftySpec fc t
cftySpec fc (CFStruct n t) = pure $ fromString n ++ "*/nonnull"
cftySpec fc (CFFun s t) = funTySpec [s] t
  where
    funTySpec : List CFType -> CFType -> Core Builder
    funTySpec args (CFFun CFWorld t) = funTySpec args t
    funTySpec args (CFFun s t) = funTySpec (s :: args) t
    funTySpec args retty
        = do rtyspec <- cftySpec fc retty
             argspecs <- traverse (cftySpec fc) (reverse . filter notWorld $ args)
             pure $ "(function (" ++ sepBy " " argspecs ++ ") " ++ rtyspec ++ ")"
cftySpec fc t = throw (GenericMsg fc ("Can't pass argument of type " ++ show t ++
                         " to foreign function"))


record CCallbackInfo where
  constructor MkCCallbackInfo
  schemeArgName : Builder
  schemeWrapName : String
  callbackBody : Builder
  argTypes : List Builder
  retType : Builder

record CWrapperDefs where
  constructor MkCWrapperDefs
  setBox : Builder
  boxDef : Builder
  cWrapDef : Builder

cCall : {auto c : Ref Ctxt Defs} ->
        {auto l : Ref Loaded (List String)} ->
        FC -> (cfn : String) -> (fnWrapName : String -> String) -> (clib : String) ->
        List (Name, CFType) -> CFType -> Core (Builder, Builder)
cCall fc cfn fnWrapName clib args ret
    = do -- loaded <- get Loaded
         -- lib <- if clib `elem` loaded
         --           then pure ""
         --           else do (fname, fullname) <- locate clib
         --                   copyLib (fname, fullname)
         --                   put Loaded (clib :: loaded)
         --                   pure ""
         argTypes <- traverse (cftySpec fc . snd) args
         retType <- cftySpec fc ret

         argsInfo <- traverse buildArg args
         argCTypes <- traverse (cType fc . snd) args
         retCType <- cType fc ret

         let cWrapperDefs = map buildCWrapperDefs $ mapMaybe snd argsInfo
         let cFunWrapDeclaration = buildCFunWrapDeclaration (fromString cfn) retCType argCTypes
         let wrapDeclarations = cFunWrapDeclaration
                                ++ concatMap (.boxDef) cWrapperDefs
                                ++ concatMap (.cWrapDef) cWrapperDefs

         let setBoxes = concatMap (.setBox) cWrapperDefs
         let call = " ((c-lambda (" ++ sepBy " " argTypes ++ ") "
                      ++ retType ++ " " ++ showB cfn ++ ") "
                      ++ sepBy " " (map fst argsInfo) ++ ")"
         let body = setBoxes ++ "\n" ++ call

         pure $ case ret of -- XXX
                     CFIORes _ => (handleRet ret body, wrapDeclarations)
                     _ => (body, wrapDeclarations)
  where
    mkNs : Int -> List CFType -> List (Maybe Builder)
    mkNs i [] = []
    mkNs i (CFWorld :: xs) = Nothing :: mkNs i xs
    mkNs i (x :: xs) = Just (fromString $ "cb" ++ show i) :: mkNs (i + 1) xs

    applyLams : Builder -> List (Maybe Builder) -> Builder
    applyLams n [] = n
    applyLams n (Nothing :: as) = applyLams ("(" ++ n ++ " #f)") as
    applyLams n (Just a :: as) = applyLams ("(" ++ n ++ " " ++ a ++ ")") as

    replaceChar : Char -> Char -> String -> String
    replaceChar old new = pack . replaceOn old new . unpack

    buildCWrapperDefs : CCallbackInfo -> CWrapperDefs
    buildCWrapperDefs (MkCCallbackInfo arg schemeWrap callbackStr argTypes retType) =
      let box = fromString $ schemeWrap ++ "-box"
          setBox = "\n (set-box! " ++ box ++ " " ++ callbackStr ++ ")"
          cWrapName = replaceChar '-' '_' schemeWrap
          boxDef = "\n(define " ++ box ++ " (box #f))\n"

          args =
            if length argTypes > 0
              then " " ++ (sepBy " " $ map (\i => fromString $ "farg-" ++ show i) [0 .. (natToInteger $ length argTypes) - 1])
              else ""

          cWrapDef : Builder =
            "\n(c-define " ++
            "(" ++ fromString schemeWrap ++ args ++ ")" ++
            " (" ++ sepBy " " argTypes ++ ")" ++
            " " ++ retType ++
            " \"" ++ fromString cWrapName ++ "\"" ++ " \"\"" ++
            "\n ((unbox " ++ box ++ ")" ++ args ++ ")" ++
            "\n)\n"
      in MkCWrapperDefs setBox boxDef cWrapDef

    buildCFunWrapDeclaration : Builder -> Builder -> List Builder -> Builder
    buildCFunWrapDeclaration name ret args =
      "\n(c-declare #<<c-declare-end\n" ++
      ret ++ " " ++ name ++ "(" ++ sepBy ", " args ++ ");" ++
      "\nc-declare-end\n)\n"

    mkFun : List CFType -> CFType -> Builder -> Builder
    mkFun args ret n
        = let argns = mkNs 0 args in
              "(lambda (" ++ sepBy " " (mapMaybe id argns) ++ ") "
              ++ (applyLams n argns ++ ")")

    callback : Builder -> List CFType -> CFType -> Core (Builder, List Builder, Builder)
    callback n args (CFFun s t) = callback n (s :: args) t
    callback n args_rev retty
        = do let args = reverse args_rev
             argTypes <- traverse (cftySpec fc) (filter notWorld args)
             retType <- cftySpec fc retty
             pure (mkFun args retty n, argTypes, retType)

    buildArg : (Name, CFType) -> Core (Builder, Maybe CCallbackInfo)
    buildArg (n, CFFun s t) = do
      let arg = schName n
      let schemeWrap = fnWrapName $ build arg
      (callbackBody, argTypes, retType) <- callback arg [s] t
      pure (fromString schemeWrap, Just $ MkCCallbackInfo arg schemeWrap callbackBody argTypes retType)
    buildArg (n, _) = pure (schName n, Nothing)

schemeCall : FC -> (sfn : String) ->
             List Name -> CFType -> Core Builder
schemeCall fc sfn argns ret
    = let call = "(" ++ fromString sfn ++ " " ++ sepBy " " (map schName argns) ++ ")" in
          case ret of
               CFIORes _ => pure $ mkWorld call
               _ => pure call

-- Use a calling convention to compile a foreign def.
-- Returns the name of the static library to link and the body
-- of the function call.
useCC : {auto c : Ref Ctxt Defs} ->
        {auto l : Ref Loaded (List String)} ->
        FC -> List String -> List (Name, CFType) -> CFType -> Core (Maybe String, Builder, Builder)
useCC fc ccs args ret
    = case parseCC ["scheme,gambit", "scheme", "C"] ccs of
           Nothing => throw (NoForeignCC fc ccs)
           Just ("scheme,gambit", [sfn]) => pure (Nothing, !(schemeCall fc sfn (map fst args) ret), "")
           Just ("scheme", [sfn]) => pure (Nothing, !(schemeCall fc sfn (map fst args) ret), "")
           Just ("C", [cfn, clib]) => do
               (call, decl) <- cCall fc cfn (fnWrapName cfn) clib args ret
               pure (Just clib, call, decl)
           Just ("C", [cfn, clib, chdr]) => do
               (call, decl) <- cCall fc cfn (fnWrapName cfn) clib args ret
               pure (Just clib, call, decl)
           _ => throw (NoForeignCC fc ccs)
  where
    fnWrapName : String -> String -> String
    fnWrapName cfn schemeArgName = schemeArgName ++ "-" ++ fromString cfn ++ "-cFunWrap"

-- For every foreign arg type, return a name, and whether to pass it to the
-- foreign call (we don't pass '%World')
mkArgs : Int -> List CFType -> List (Name, Bool)
mkArgs i [] = []
mkArgs i (CFWorld :: cs) = (MN "farg" i, False) :: mkArgs i cs
mkArgs i (c :: cs) = (MN "farg" i, True) :: mkArgs (i + 1) cs

mkStruct : {auto s : Ref Structs (List String)} ->
           CFType -> Core Builder
mkStruct (CFStruct n flds)
    = do defs <- traverse mkStruct (map snd flds)
         strs <- get Structs
         if n `elem` strs
            then pure (concat defs)
            else do put Structs (n :: strs)
                    pure $ concat defs ++ "(define-c-struct " ++ fromString n ++ " "
                           ++ sepBy " " !(traverse showFld flds) ++ ")\n"
  where
    showFld : (String, CFType) -> Core Builder
    showFld (n, ty) = pure $ "(" ++ fromString n ++ " " ++ !(cftySpec emptyFC ty) ++ ")"
mkStruct (CFIORes t) = mkStruct t
mkStruct (CFFun a b) = [| mkStruct a ++ mkStruct b |]
mkStruct _ = pure ""

schFgnDef : {auto c : Ref Ctxt Defs} ->
            {auto l : Ref Loaded (List String)} ->
            {auto s : Ref Structs (List String)} ->
            FC -> Name -> NamedDef -> Core (Maybe String, Builder)
schFgnDef fc n (MkNmForeign cs args ret)
    = do let argns = mkArgs 0 args
         let allargns = map fst argns
         let useargns = map fst (filter snd argns)
         argStrs <- traverse mkStruct args
         retStr <- mkStruct ret
         (lib, body, wrapDeclarations) <- useCC fc cs (zip useargns args) ret
         defs <- get Ctxt
         pure (lib,
                concat argStrs ++ retStr ++
                wrapDeclarations ++
                "(define " ++ schName !(full (gamma defs) n) ++
                " (lambda (" ++ sepBy " " (map schName allargns) ++ ") " ++
                body ++ "))\n")
schFgnDef _ _ _ = pure (Nothing, "")

getFgnCall : {auto c : Ref Ctxt Defs} ->
             {auto l : Ref Loaded (List String)} ->
             {auto s : Ref Structs (List String)} ->
             (Name, FC, NamedDef) -> Core (Maybe String, Builder)
getFgnCall (n, fc, d) = schFgnDef fc n d

compileToSCM : Ref Ctxt Defs ->
               ClosedTerm -> (outfile : String) -> Core (List String)
compileToSCM c tm outfile
    = do cdata <- getCompileData False Cases tm
         let ndefs = namedDefs cdata
         -- let tags = nameTags cdata
         let ctm = forget (mainExpr cdata)

         ds <- getDirectives Gambit
         let schLazy = if getWeakMemoLazy ds then weakMemoLaziness else defaultLaziness

         defs <- get Ctxt
         l <- newRef {t = List String} Loaded []
         s <- newRef {t = List String} Structs []
         fgndefs <- traverse getFgnCall ndefs
         (sortedDefs, constants) <- sortDefs ndefs
         compdefs <- traverse (getScheme constants (gambitPrim constants schLazy) gambitString schLazy) ndefs
         let code = concat (map snd fgndefs) ++ concat compdefs
         main <- schExp constants (gambitPrim constants schLazy) gambitString schLazy 0 ctm
         support <- readDataFile "gambit/support.scm"
         extraRuntime <- getExtraRuntime ds
         foreign <- readDataFile "gambit/foreign.scm"
         let scm = sepBy "\n" [schHeader, fromString support, fromString extraRuntime, fromString foreign, code, main]
         Right () <- coreLift $ writeFile outfile $ build scm
            | Left err => throw (FileErr outfile err)
         pure $ mapMaybe fst fgndefs

compileExpr :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) -> (outputDir : String) ->
  ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c s tmpDir outputDir tm outfile
    = do let srcPath = tmpDir </> outfile <.> "scm"
         let execPath = outputDir </> outfile
         libsname <- compileToSCM c tm srcPath
         libsfile <- traverse findLibraryFile $ map (<.> "a") (nub libsname)
         gsc <- coreLift findGSC
         gscBackend <- coreLift findGSCBackend
         ds <- getDirectives Gambit
         let gscCompileOpts =
             case find (== "C") ds of
                 Nothing => gscBackend ++ ["-exe", "-cc-options", "-Wno-implicit-function-declaration", "-ld-options"] ++ libsfile
                 Just _ => ["-c"]
         let cmd = gsc ++ gscCompileOpts ++ ["-o", execPath, srcPath]
         ok <- coreLift $ system cmd
         if ok == 0
            then pure (Just execPath)
            else pure Nothing

executeExpr :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c s tmpDir tm
    = do Just sh <- compileExpr c s tmpDir tmpDir tm "_tmpgambit"
           | Nothing => throw (InternalError "compileExpr returned Nothing")
         coreLift_ $ system [sh] -- TODO: on windows, should add exe extension
         pure ()

export
codegenGambit : Codegen
codegenGambit = MkCG compileExpr executeExpr Nothing Nothing
