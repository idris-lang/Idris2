module Yaffle.Main

import Parser.Source

import Core.Binary
import Core.Context
import Core.Directory
import Core.Env
import Core.FC
import Core.InitPrimitives
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.TT
import Core.UnifyState
import Libraries.Utils.Path

import TTImp.Parser
import TTImp.ProcessDecls
import TTImp.TTImp

import Yaffle.REPL

import Data.List
import Data.So
import Data.Strings
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
yaffleMain fname args
    = do defs <- initDefs
         c <- newRef Ctxt defs
         t <- processArgs args
         modIdent <- ctxtPathToNS fname
         m <- newRef MD (initMetadata (PhysicalIdrSrc modIdent))
         u <- newRef UST initUState
         setLogTimings t
         addPrimitives
         case extension fname of
              Just "ttc" => do coreLift_ $ putStrLn "Processing as TTC"
                               ignore $ readFromTTC {extra = ()} True emptyFC True fname (nsAsModuleIdent emptyNS) emptyNS
                               coreLift_ $ putStrLn "Read TTC"
              _ => do coreLift_ $ putStrLn "Processing as TTImp"
                      ok <- processTTImpFile fname
                      when ok $
                         do makeBuildDirectory modIdent
                            writeToTTC () !(getTTCFileName fname "ttc")
                            coreLift_ $ putStrLn "Written TTC"
         ust <- get UST

         repl {c} {u}

ymain : IO ()
ymain
    = do (_ :: fname :: rest) <- getArgs
             | _ => do putStrLn usage
                       exitWith (ExitFailure 1)
         coreRun (yaffleMain fname rest)
               (\err : Error => putStrLn ("Uncaught error: " ++ show err))
               (\res => pure ())
