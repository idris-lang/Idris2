module Idris.Error

import Core.CaseTree
import Core.Core
import Core.Context
import Core.Env
import Core.Options
import Core.Value

import Idris.REPLOpts
import Idris.Resugar
import Idris.Syntax

import Parser.Source

import Data.List
import Data.List.Extra
import Data.Maybe
import Data.Stream
import Data.Strings
import System.File

%default covering

pshow : {vars : _} ->
        {auto c : Ref Ctxt Defs} ->
        {auto s : Ref Syn SyntaxInfo} ->
        Env Term vars -> Term vars -> Core String
pshow env tm
    = do defs <- get Ctxt
         itm <- resugar env !(normaliseHoles defs env tm)
         pure (show itm)

pshowNoNorm : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Env Term vars -> Term vars -> Core String
pshowNoNorm env tm
    = do defs <- get Ctxt
         itm <- resugar env tm
         pure (show itm)

ploc : {auto o : Ref ROpts REPLOpts} ->
       FC -> Core String
ploc EmptyFC = pure ""
ploc (MkFC _ s e) = do
    let sr = integerToNat $ cast $ fst s
    let sc = integerToNat $ cast $ snd s
    let er = integerToNat $ cast $ fst e
    let ec = integerToNat $ cast $ snd e
    source <- lines <$> getCurrentElabSource
    pure $ if sr == er
              then show (sr + 1) ++ "\t" ++ fromMaybe "" (elemAt source sr)
                   ++ "\n\t" ++ repeatChar sc ' ' ++ repeatChar (ec `minus` sc) '^' ++ "\n"
              else addLineNumbers sr $ extractRange sr er source
  where
    extractRange : Nat -> Nat -> List a -> List a
    extractRange s e xs = take ((e `minus` s) + 1) (drop s xs)
    repeatChar : Nat -> Char -> String
    repeatChar n c = pack $ take n (repeat c)
    addLineNumbers : Nat -> List String -> String
    addLineNumbers st xs = snd $ foldl (\(i, s), l => (S i, s ++ show (i + 1) ++ "\t" ++ l ++ "\n")) (st, "") xs

export
perror : {auto c : Ref Ctxt Defs} ->
         {auto s : Ref Syn SyntaxInfo} ->
         {auto o : Ref ROpts REPLOpts} ->
         Error -> Core String
perror (Fatal err) = perror err
perror (CantConvert fc env l r)
    = pure $ "Mismatch between:\n\t" ++ !(pshow env l) ++ "\nand\n\t" ++ !(pshow env r) ++ "\nat:\n" ++ !(ploc fc)
perror (CantSolveEq fc env l r)
    = pure $ "Can't solve constraint between:\n\t" ++ !(pshow env l) ++
      "\nand\n\t" ++ !(pshow env r) ++ "\nat:\n" ++ !(ploc fc)
perror (PatternVariableUnifies fc env n tm)
    = pure $ "Pattern variable " ++ showPVar n ++
      " unifies with:\n\t" ++ !(pshow env tm) ++ "\nat:\n" ++ !(ploc fc)
  where
    showPVar : Name -> String
    showPVar (PV n _) = showPVar n
    showPVar n = show n
perror (CyclicMeta fc env n tm)
    = pure $ "Cycle detected in solution of metavariable "
               ++ show !(prettyName n) ++ " = "
               ++ !(pshow env tm) ++ " at:\n" ++ !(ploc fc)
perror (WhenUnifying _ env x y err)
    = pure $ "When unifying " ++ !(pshow env x) ++ " and " ++ !(pshow env y) ++ "\n"
       ++ !(perror err)
perror (ValidCase fc env (Left tm))
    = pure $ !(pshow env tm) ++ " is not a valid impossible case at:\n" ++ !(ploc fc)
perror (ValidCase _ env (Right err))
    = pure $ "Impossible pattern gives an error:\n" ++ !(perror err)
perror (UndefinedName fc x) = pure $ "Undefined name " ++ show x ++ " at:\n" ++ !(ploc fc)
perror (InvisibleName fc n (Just ns))
    = pure $ "Name " ++ show n ++ " is inaccessible since " ++
             showSep "." (reverse ns) ++ " is not explicitly imported at:\n" ++ !(ploc fc)
perror (InvisibleName fc x Nothing)
    = pure $ "Name " ++ show x ++ " is private at:\n" ++ !(ploc fc)
perror (BadTypeConType fc n)
    = pure $ "Return type of " ++ show n ++ " must be Type at:\n" ++ !(ploc fc)
perror (BadDataConType fc n fam)
    = pure $ "Return type of " ++ show n ++ " must be in "
                 ++ show !(toFullNames fam) ++ " at:\n" ++ !(ploc fc)
perror (NotCovering fc n IsCovering)
    = pure $ "Internal error (Coverage of " ++ show n ++ ")"
perror (NotCovering fc n (MissingCases cs))
    = pure $ !(prettyName n) ++ " is not covering at:\n" ++ !(ploc fc) ++ "Missing cases:\n\t" ++
             showSep "\n\t" !(traverse (pshow []) cs)
perror (NotCovering fc n (NonCoveringCall ns))
    = pure $ !(prettyName n) ++ " is not covering at:\n" ++ !(ploc fc) ++ "\n\t" ++
                "Calls non covering function"
                   ++ case ns of
                           [fn] => " " ++ show fn
                           _ => "s: " ++ showSep ", " (map show ns)
perror (NotTotal fc n r)
    = pure $ !(prettyName n) ++ " is not total:\n\t" ++ show r ++ "\nat:\n" ++ !(ploc fc)
perror (LinearUsed fc count n)
    = pure $ "There are " ++ show count ++ " uses of linear name " ++ sugarName n ++ " at:\n" ++ !(ploc fc)
perror (LinearMisuse fc n exp ctx)
    = if isErased exp
         then pure $ show n ++ " is not accessible in this context at:\n" ++ !(ploc fc)
         else pure $ "Trying to use " ++ showRig exp ++ " name " ++ sugarName n ++
                 " in " ++ showRel ctx ++ " context at:\n" ++ !(ploc fc)
  where
    showRig : RigCount -> String
    showRig = elimSemi "irrelevant"
                       "linear"
                       (const "unrestricted")

    showRel : RigCount -> String
    showRel = elimSemi "irrelevant"
                       "relevant"
                       (const "non-linear")
perror (BorrowPartial fc env tm arg)
    = pure $ !(pshow env tm) ++
             " borrows argument " ++ !(pshow env arg) ++
             " so must be fully applied at:\n" ++ !(ploc fc)
perror (BorrowPartialType fc env tm)
    = pure $ !(pshow env tm) ++
             " borrows, so must return a concrete type at:\n" ++ !(ploc fc)
perror (AmbiguousName fc ns) = pure $ "Ambiguous name " ++ show ns ++ " at:\n" ++ !(ploc fc)
perror (AmbiguousElab fc env ts)
    = do pp <- getPPrint
         setPPrint (record { fullNamespace = True } pp)
         let res = "Ambiguous elaboration at:\n" ++ !(ploc fc) ++ "Possible correct results:\n\t" ++
                   showSep "\n\t" !(traverse (pshow env) ts)
         setPPrint pp
         pure res
perror (AmbiguousSearch fc env tgt ts)
    = pure $ "Multiple solutions found in search of:\n\t"
           ++ !(pshowNoNorm env tgt)
           ++ "\nat:\n" ++ !(ploc fc)
           ++ "\nPossible correct results:\n\t" ++
           showSep "\n\t" !(traverse (pshowNoNorm env) ts)
perror (AmbiguityTooDeep fc n ns)
    = pure $ "Maximum ambiguity depth exceeded in "  ++ show !(getFullName n)
             ++ ": " ++ showSep " --> " (map show !(traverse getFullName ns)) ++ " at:\n" ++ !(ploc fc)
perror (AllFailed ts)
    = case allUndefined ts of
           Just e => perror e
           _ => pure $ "Sorry, I can't find any elaboration which works. All errors:\n" ++
                     showSep "\n" !(traverse pAlterror ts)
  where
    pAlterror : (Maybe Name, Error) -> Core String
    pAlterror (Just n, err)
       = pure $ "If " ++ show !(aliasName !(getFullName n)) ++ ": "
                      ++ !(perror err) ++ "\n"
    pAlterror (Nothing, err)
       = pure $ "Possible error:\n\t" ++ !(perror err)

    allUndefined : List (Maybe Name, Error) -> Maybe Error
    allUndefined [] = Nothing
    allUndefined [(_, UndefinedName loc e)] = Just (UndefinedName loc e)
    allUndefined ((_, UndefinedName _ e) :: es) = allUndefined es
    allUndefined _ = Nothing
perror (RecordTypeNeeded fc _)
    = pure $ "Can't infer type for this record update at:\n" ++ !(ploc fc)
perror (NotRecordField fc fld Nothing)
    = pure $ fld ++ " is not part of a record type at:\n" ++ !(ploc fc)
perror (NotRecordField fc fld (Just ty))
    = pure $ "Record type " ++ show !(getFullName ty) ++ " has no field " ++ fld ++ " at:\n" ++ !(ploc fc)
perror (NotRecordType fc ty)
    = pure $ show !(getFullName ty) ++ " is not a record type at:\n" ++ !(ploc fc)
perror (IncompatibleFieldUpdate fc flds)
    = pure $ "Field update " ++ showSep "->" flds ++
             " not compatible with other updates at:\n" ++ !(ploc fc)
perror (InvalidImplicits fc env [Just n] tm)
    = pure $ show n ++ " is not a valid implicit argument in " ++ !(pshow env tm) ++ " at:\n" ++ !(ploc fc)
perror (InvalidImplicits fc env ns tm)
    = pure $ showSep ", " (map show ns) ++
             " are not valid implicit arguments in " ++ !(pshow env tm) ++ " at:\n" ++ !(ploc fc)
perror (TryWithImplicits fc env imps)
    = pure $ "Need to bind implicits "
             ++ showSep ", " !(traverse (tshow env) imps) ++ " at:\n" ++ !(ploc fc)
  where
    tshow : {vars : _} ->
            Env Term vars -> (Name, Term vars) -> Core String
    tshow env (n, ty) = pure $ show n ++ " : " ++ !(pshow env ty)
perror (BadUnboundImplicit fc env n ty)
    = pure $ "Can't bind name " ++ nameRoot n ++ " with type " ++ !(pshow env ty)
               ++ " here at:\n" ++ !(ploc fc) ++ "Try binding explicitly."
perror (CantSolveGoal fc env g)
    = let (_ ** (env', g')) = dropEnv env g in
          pure $ "Can't find an implementation for " ++ !(pshow env' g') ++ " at:\n" ++ !(ploc fc)
  where
    -- For display, we don't want to see the full top level type; just the
    -- return type
    dropEnv : {vars : _} ->
              Env Term vars -> Term vars ->
              (ns ** (Env Term ns, Term ns))
    dropEnv env (Bind _ n b@(Pi _ _ _) sc) = dropEnv (b :: env) sc
    dropEnv env (Bind _ n b@(Let _ _ _) sc) = dropEnv (b :: env) sc
    dropEnv env tm = (_ ** (env, tm))

perror (DeterminingArg fc n i env g)
    = pure $ "Can't find an implementation for " ++ !(pshow env g) ++ "\n" ++
             "since I can't infer a value for argument " ++ show n ++ " at:\n" ++ !(ploc fc)
perror (UnsolvedHoles hs)
    = pure $ "Unsolved holes:\n" ++ showHoles hs
  where
    showHoles : List (FC, Name) -> String
    showHoles [] = ""
    showHoles ((fc, n) :: hs) = show n ++ " introduced at " ++ show fc ++ "\n"
                                       ++ showHoles hs
perror (CantInferArgType fc env n h ty)
    = pure $ "Can't infer type for argument " ++ show n ++ "\n" ++
             "Got " ++ !(pshow env ty) ++ " with hole " ++ show h ++ " at:\n" ++ !(ploc fc)
perror (SolvedNamedHole fc env h tm)
    = pure $ "Named hole " ++ show h ++ " has been solved by unification\n"
              ++ "Result: " ++ !(pshow env tm) ++ " at:\n" ++ !(ploc fc)
perror (VisibilityError fc vx x vy y)
    = pure $ show vx ++ " " ++ sugarName !(toFullNames x) ++
             " cannot refer to " ++ show vy ++ " " ++ sugarName !(toFullNames y) ++ " at:\n" ++ !(ploc fc)
perror (NonLinearPattern fc n) = pure $ "Non linear pattern " ++ sugarName n ++ " at:\n" ++ !(ploc fc)
perror (BadPattern fc n) = pure $ "Pattern not allowed here: " ++ show n ++ " at:\n" ++ !(ploc fc)
perror (NoDeclaration fc n) = pure $ "No type declaration for " ++ show n ++ " at:\n" ++ !(ploc fc)
perror (AlreadyDefined fc n) = pure $ show n ++ " is already defined"
perror (NotFunctionType fc env tm)
    = pure $ !(pshow env tm) ++ " is not a function type at:\n" ++ !(ploc fc)
perror (RewriteNoChange fc env rule ty)
    = pure $ "Rewriting by " ++ !(pshow env rule) ++
             " did not change type " ++ !(pshow env ty) ++ " at:\n" ++ !(ploc fc)
perror (NotRewriteRule fc env rule)
    = pure $ !(pshow env rule) ++ " is not a rewrite rule type at:\n" ++ !(ploc fc)
perror (CaseCompile fc n DifferingArgNumbers)
    = pure $ "Patterns for " ++ !(prettyName n) ++ " have differing numbers of arguments at:\n" ++ !(ploc fc)
perror (CaseCompile fc n DifferingTypes)
    = pure $ "Patterns for " ++ !(prettyName n) ++ " require matching on different types at:\n" ++ !(ploc fc)
perror (CaseCompile fc n UnknownType)
    = pure $ "Can't infer type to match in " ++ !(prettyName n) ++ " at:\n" ++ !(ploc fc)
perror (CaseCompile fc n (NotFullyApplied cn))
    = pure $ "Constructor " ++ show !(toFullNames cn) ++ " is not fully applied at:\n" ++ !(ploc fc)
perror (CaseCompile fc n (MatchErased (_ ** (env, tm))))
    = pure $ "Attempt to match on erased argument " ++ !(pshow env tm) ++
             " in " ++ !(prettyName n) ++ " at\n:" ++ !(ploc fc)
perror (BadDotPattern fc env reason x y)
    = pure $ "Can't match on " ++ !(pshow env x) ++
           " (" ++ show reason ++ ") at\n" ++ !(ploc fc)
perror (MatchTooSpecific fc env tm)
    = pure $ "Can't match on " ++ !(pshow env tm) ++
             " as it has a polymorphic type at:\n" ++ !(ploc fc)
perror (BadImplicit fc str)
    = pure $ "Can't infer type for unbound implicit name " ++ str ++ " at\n" ++
             !(ploc fc) ++ "Try making it a bound implicit."
perror (BadRunElab fc env script)
    = pure $ "Bad elaborator script " ++ !(pshow env script) ++ " at:\n" ++ !(ploc fc)
perror (GenericMsg fc str) = pure $ str ++ " at:\n" ++ !(ploc fc)
perror (TTCError msg) = pure $ "Error in TTC file: " ++ show msg ++ " (the most likely case is that the ./build directory in your current project contains files from a previous build of idris2 or the idris2 executable is from a different build than the installed .ttc files)"
perror (FileErr fname err)
    = pure $ "File error in " ++ fname ++ ": " ++ show err
perror (ParseFail _ err)
    = pure $ show err
perror (ModuleNotFound _ ns)
    = pure $ showSep "." (reverse ns) ++ " not found"
perror (CyclicImports ns)
    = pure $ "Module imports form a cycle: " ++ showSep " -> " (map showMod ns)
  where
    showMod : List String -> String
    showMod ns = showSep "." (reverse ns)
perror ForceNeeded = pure "Internal error when resolving implicit laziness"
perror (InternalError str) = pure $ "INTERNAL ERROR: " ++ str
perror (UserError str) = pure $ "Error: " ++ str

perror (InType fc n err)
    = pure $ "While processing type of " ++ !(prettyName n) ++
             " at " ++ show fc ++ ":\n" ++ !(perror err)
perror (InCon fc n err)
    = pure $ "While processing constructor " ++ !(prettyName n) ++
             " at " ++ show fc ++ ":\n" ++ !(perror err)
perror (InLHS fc n err)
    = pure $ "While processing left hand side of " ++ !(prettyName n) ++
             " at " ++ show fc ++ ":\n" ++ !(perror err)
perror (InRHS fc n err)
    = pure $ "While processing right hand side of " ++ !(prettyName n) ++
             " at " ++ show fc ++ ":\n" ++ !(perror err)

export
pwarning : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           Warning -> Core String
pwarning (UnreachableClause fc env tm)
    = pure $ "Warning: unreachable clause: " ++ !(pshow env tm)

export
display : {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto o : Ref ROpts REPLOpts} ->
          Error -> Core String
display err
    = pure $ maybe "" (\f => show f ++ ":") (getErrorLoc err) ++
                   !(perror err)

export
displayWarning : {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 Warning -> Core String
displayWarning w
    = pure $ maybe "" (\f => show f ++ ":") (getWarningLoc w) ++
                   !(pwarning w)
