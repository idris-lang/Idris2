module Yaffle.Main

import Core.Binary
import Core.Context
import Core.Directory
import Core.FC
import Core.InitPrimitives
import Core.Metadata
import Core.UnifyState
import Libraries.Utils.Path

import Idris.Syntax

import TTImp.ProcessDecls

import Yaffle.REPL

import System

%default covering

usage : String
usage = "Usage: yaffle <input file> [--timing]"

processArgs : List String -> Core Bool
processArgs [] = pure False
processArgs ["--timing"] = pure True
processArgs _
    = coreLift $ do ignore $ putStrLn usage
                    exitWith (ExitFailure 1)

HasNames () where
  full _ _ = pure ()
  resolved _ _ = pure ()

export
yaffleMain : String -> List String -> Core ()
yaffleMain sourceFileName args
    = do defs <- initDefs
         c <- newRef Ctxt defs
         t <- processArgs args
         modIdent <- ctxtPathToNS sourceFileName
         m <- newRef MD (initMetadata (PhysicalIdrSrc modIdent))
         u <- newRef UST initUState
         s <- newRef Syn initSyntax
         setLogTimings t
         addPrimitives
         case extension sourceFileName of
              Just "ttc" => do coreLift_ $ putStrLn "Processing as TTC"
                               ignore $ readFromTTC {extra = ()} True emptyFC True sourceFileName (nsAsModuleIdent emptyNS) emptyNS
                               coreLift_ $ putStrLn "Read TTC"
              _ => do coreLift_ $ putStrLn "Processing as TTImp"
                      ok <- processTTImpFile sourceFileName
                      when ok $
                         do makeBuildDirectory modIdent
                            ttcFileName <- getTTCFileName sourceFileName "ttc"
                            writeToTTC () sourceFileName ttcFileName
                            coreLift_ $ putStrLn "Written TTC"
         ust <- get UST

         repl {c} {u} {s}

ymain : IO ()
ymain
    = do (_ :: fname :: rest) <- getArgs
             | _ => do putStrLn usage
                       exitWith (ExitFailure 1)
         coreRun (yaffleMain fname rest)
               (\err : Error => putStrLn ("Uncaught error: " ++ show err))
               (\res => pure ())
