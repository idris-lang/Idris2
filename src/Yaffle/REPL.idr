module Yaffle.REPL

import Core.AutoSearch
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.FC
import Core.Metadata
import Core.Normalise
import Core.Termination
import Core.TT
import Core.Unify
import Core.Value

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Interactive.ExprSearch
import TTImp.Interactive.GenerateDef
import TTImp.Parser
import TTImp.ProcessDecls
import TTImp.TTImp
import TTImp.Unelab

import Parser.Source

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
          ImpREPL -> Core Bool
process (Eval ttimp)
    = do (tm, _) <- elabTerm 0 InExpr [] (MkNested []) [] ttimp Nothing
         defs <- get Ctxt
         tmnf <- normalise defs [] tm
         coreLift_ (printLn !(unelab [] tmnf))
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
             ty <- normaliseHoles defs [] tyh
             coreLift_ $ putStrLn $ show n ++ " : " ++
                                    show !(unelab [] ty)
process (Check ttimp)
    = do (tm, gty) <- elabTerm 0 InExpr [] (MkNested []) [] ttimp Nothing
         defs <- get Ctxt
         tyh <- getTerm gty
         ty <- normaliseHoles defs [] tyh
         coreLift_ (printLn !(unelab [] ty))
         pure True
process (ProofSearch n_in)
    = do defs <- get Ctxt
         [(n, i, ty)] <- lookupTyName n_in (gamma defs)
              | [] => undefinedName toplevelFC n_in
              | ns => throw (AmbiguousName toplevelFC (map fst ns))
         def <- search toplevelFC top False 1000 n ty []
         defs <- get Ctxt
         defnf <- normaliseHoles defs [] def
         coreLift_ (printLn !(toFullNames defnf))
         pure True
process (ExprSearch n_in)
    = do defs <- get Ctxt
         [(n, i, ty)] <- lookupTyName n_in (gamma defs)
              | [] => undefinedName toplevelFC n_in
              | ns => throw (AmbiguousName toplevelFC (map fst ns))
         results <- exprSearchN toplevelFC 1 n []
         traverse_ (\d => coreLift (printLn d)) results
         pure True
process (GenerateDef line name)
    = do defs <- get Ctxt
         Just (_, n', _, _) <- findTyDeclAt (\p, n => onLine line p)
              | Nothing => do coreLift_ (putStrLn ("Can't find declaration for " ++ show name))
                              pure True
         case !(lookupDefExact n' (gamma defs)) of
              Just None =>
                  catch
                    (do ((fc, cs) :: _) <- logTime "Generation" $
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
                             the (Core ()) $ case isCovering tot of
                                  MissingCases cs =>
                                     coreLift_ (putStrLn (show fn ++ ":\n" ++
                                                 showSep "\n" (map show cs)))
                                  NonCoveringCall ns =>
                                     coreLift_ (putStrLn
                                         (show fn ++ ": Calls non covering function"
                                           ++ case ns of
                                                   [fn] => " " ++ show fn
                                                   _ => "s: " ++ showSep ", " (map show ns)))
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
               ImpREPL -> Core Bool
processCatch cmd
    = catch (process cmd)
            (\err => do coreLift_ (putStrLn (show err))
                        pure True)

export
repl : {auto c : Ref Ctxt Defs} ->
       {auto m : Ref MD Metadata} ->
       {auto u : Ref UST UState} ->
       Core ()
repl
    = do coreLift_ (putStr "Yaffle> ")
         inp <- coreLift getLine
         case runParser "(interactive)" Nothing inp command of
              Left err => do coreLift_ (printLn err)
                             repl
              Right cmd => when !(processCatch cmd) repl
