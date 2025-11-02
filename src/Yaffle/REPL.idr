module Yaffle.REPL

import Core.AutoSearch
import Core.Env
import Core.Metadata
import Core.Termination
import Core.Unify

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Interactive.ExprSearch
import TTImp.Interactive.GenerateDef
import TTImp.Parser
import TTImp.ProcessDecls
import TTImp.TTImp
import TTImp.Unelab

import Parser.Source

import Data.String

%default covering

showInfo : (Name, Int, GlobalDef) -> Core ()
showInfo (n, _, d)
    = coreLift_ $ putStrLn (show n ++ " ==>\n" ++
                   "\t" ++ show (definition d) ++ "\n" ++
                   "\t" ++ show (sizeChange d) ++ "\n")

-- Returns 'True' if the REPL should continue
process : {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto o : Ref ROpts REPLOpts} ->
          ImpREPL -> Core Bool
process (Eval ttimp)
    = do (tm, _) <- elabTerm 0 InExpr [] (MkNested []) Env.empty ttimp Nothing
         defs <- get Ctxt
         tmnf <- normalise defs Env.empty tm
         coreLift_ (printLn !(unelab Env.empty tmnf))
         pure True
process (Check (IVar _ n))
    = do defs <- get Ctxt
         ns <- lookupTyName n (gamma defs)
         traverse_ printName ns
         pure True
  where
    printName : (Name, Int, ClosedTerm) -> Core ()
    printName (n, _, tyh)
        = do defs <- get Ctxt
             ty <- normaliseHoles defs Env.empty tyh
             coreLift_ $ putStrLn $ show n ++ " : " ++
                                    show !(unelab Env.empty ty)
process (Check ttimp)
    = do (tm, gty) <- elabTerm 0 InExpr [] (MkNested []) Env.empty ttimp Nothing
         defs <- get Ctxt
         tyh <- getTerm gty
         ty <- normaliseHoles defs Env.empty tyh
         coreLift_ (printLn !(unelab Env.empty ty))
         pure True
process (ProofSearch n_in)
    = do defs <- get Ctxt
         [(n, i, ty)] <- lookupTyName n_in (gamma defs)
              | ns => ambiguousName (justFC defaultFC) n_in (map fst ns)
         def <- search (justFC defaultFC) top False 1000 n ty Env.empty
         defs <- get Ctxt
         defnf <- normaliseHoles defs Env.empty def
         coreLift_ (printLn !(toFullNames defnf))
         pure True
process (ExprSearch n_in)
    = do defs <- get Ctxt
         [(n, i, ty)] <- lookupTyName n_in (gamma defs)
              | ns => ambiguousName (justFC defaultFC) n_in (map fst ns)
         results <- exprSearchN (justFC defaultFC) 1 n []
         traverse_ (coreLift . printLn) results
         pure True
process (GenerateDef line name)
    = do defs <- get Ctxt
         Just (_, n', _, _) <- findTyDeclAt (\p, n => onLine line p)
              | Nothing => do coreLift_ (putStrLn ("Can't find declaration for " ++ show name))
                              pure True
         case !(lookupDefExact n' (gamma defs)) of
              Just None =>
                  catch
                    (do ((fc, cs) :: _) <- logTime 0 "Generation" $
                                makeDefN (\p, n => onLine line p) 1 n'
                           | _ => coreLift_ (putStrLn "Failed")
                        coreLift_ $ putStrLn (show cs))
                    (\err => coreLift_ $ putStrLn $ "Can't find a definition for " ++ show n')
              Just _ => coreLift_ $ putStrLn "Already defined"
              Nothing => coreLift_ $ putStrLn $ "Can't find declaration for " ++ show name
         pure True
process (Missing n_in)
    = do defs <- get Ctxt
         case !(lookupCtxtName n_in (gamma defs)) of
              [] => undefinedName emptyFC n_in
              ts => do traverse_ (\fn =>
                          do tot <- getTotality emptyFC fn
                             case isCovering tot of
                                  MissingCases cs =>
                                     coreLift_ (putStrLn (show fn ++ ":\n" ++
                                                 joinBy "\n" (map show cs)))
                                  NonCoveringCall ns =>
                                     coreLift_ (putStrLn
                                         (show fn ++ ": Calls non covering function"
                                           ++ case ns of
                                                   [fn] => " " ++ show fn
                                                   _ => "s: " ++ joinBy ", " (map show ns)))
                                  _ => coreLift_ $ putStrLn (show fn ++ ": All cases covered"))
                        (map fst ts)
                       pure True
process (CheckTotal n)
    = do defs <- get Ctxt
         case !(lookupCtxtName n (gamma defs)) of
              [] => undefinedName emptyFC n
              ts => do traverse_ (\fn =>
                          do ignore $ checkTotal emptyFC fn
                             tot <- getTotality emptyFC fn
                             coreLift_ (putStrLn (show fn ++ " is " ++ show tot)))
                               (map fst ts)
                       pure True
process (DebugInfo n)
    = do defs <- get Ctxt
         traverse_ showInfo !(lookupCtxtName n (gamma defs))
         pure True
process Quit
    = do coreLift_ $ putStrLn "Bye for now!"
         pure False

processCatch : {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto o : Ref ROpts REPLOpts} ->
               ImpREPL -> Core Bool
processCatch cmd
    = catch (process cmd)
            (\err => do coreLift_ (putStrLn (show err))
                        pure True)

export
repl : {auto c : Ref Ctxt Defs} ->
       {auto m : Ref MD Metadata} ->
       {auto u : Ref UST UState} ->
       {auto s : Ref Syn SyntaxInfo} ->
       {auto o : Ref ROpts REPLOpts} ->
       Core ()
repl
    = do coreLift_ (putStr "Yaffle> ")
         inp <- coreLift getLine
         case runParser (Virtual Interactive) Nothing inp command of
              Left err => do coreLift_ (printLn err)
                             repl
              Right (_, _, cmd) => when !(processCatch cmd) repl
