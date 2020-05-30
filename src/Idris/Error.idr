module Idris.Error

import Core.CaseTree
import Core.Core
import Core.Context
import Core.Env
import Core.Options

import Idris.Resugar
import Idris.Syntax

import Parser.Source

import Data.List
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

export
perror : {auto c : Ref Ctxt Defs} ->
         {auto s : Ref Syn SyntaxInfo} ->
         Error -> Core String
perror (Fatal err) = perror err
perror (CantConvert _ env l r)
    = pure $ "Mismatch between:\n\t" ++ !(pshow env l) ++ "\nand\n\t" ++ !(pshow env r)
perror (CantSolveEq _ env l r)
    = pure $ "Can't solve constraint between:\n\t" ++ !(pshow env l) ++
      "\nand\n\t" ++ !(pshow env r)
perror (PatternVariableUnifies _ env n tm)
    = pure $ "Pattern variable " ++ showPVar n ++
      " unifies with:\n\t" ++ !(pshow env tm)
  where
    showPVar : Name -> String
    showPVar (PV n _) = showPVar n
    showPVar n = show n
perror (CyclicMeta _ env n tm)
    = pure $ "Cycle detected in solution of metavariable "
               ++ show !(prettyName n) ++ " = "
               ++ !(pshow env tm)
perror (WhenUnifying _ env x y err)
    = pure $ "When unifying " ++ !(pshow env x) ++ " and " ++ !(pshow env y) ++ "\n"
       ++ !(perror err)
perror (ValidCase _ env (Left tm))
    = pure $ !(pshow env tm) ++ " is not a valid impossible case"
perror (ValidCase _ env (Right err))
    = pure $ "Impossible pattern gives an error:\n" ++ !(perror err)
perror (UndefinedName _ x) = pure $ "Undefined name " ++ show x
perror (InvisibleName _ n (Just ns))
    = pure $ "Name " ++ show n ++ " is inaccessible since " ++
             showSep "." (reverse ns) ++ " is not explicitly imported"
perror (InvisibleName _ x Nothing)
    = pure $ "Name " ++ show x ++ " is private"
perror (BadTypeConType fc n)
    = pure $ "Return type of " ++ show n ++ " must be Type"
perror (BadDataConType fc n fam)
    = pure $ "Return type of " ++ show n ++ " must be in " ++ show fam
perror (NotCovering fc n IsCovering)
    = pure $ "Internal error (Coverage of " ++ show n ++ ")"
perror (NotCovering fc n (MissingCases cs))
    = pure $ !(prettyName n) ++ " is not covering. Missing cases:\n\t" ++
             showSep "\n\t" !(traverse (pshow []) cs)
perror (NotCovering fc n (NonCoveringCall ns))
    = pure $ !(prettyName n) ++ " is not covering:\n\t" ++
                "Calls non covering function"
                   ++ case ns of
                           [fn] => " " ++ show fn
                           _ => "s: " ++ showSep ", " (map show ns)
perror (NotTotal fc n r)
    = pure $ !(prettyName n) ++ " is not total:\n\t" ++ show r
perror (LinearUsed fc count n)
    = pure $ "There are " ++ show count ++ " uses of linear name " ++ sugarName n
perror (LinearMisuse fc n exp ctx)
    = pure $ if isErased exp
         then show n ++ " is not accessible in this context"
         else "Trying to use " ++ showRig exp ++ " name " ++ sugarName n ++
                 " in " ++ showRel ctx ++ " context"
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
             " so must be fully applied"
perror (BorrowPartialType fc env tm)
    = pure $ !(pshow env tm) ++
             " borrows, so must return a concrete type"
perror (AmbiguousName fc ns) = pure $ "Ambiguous name " ++ show ns
perror (AmbiguousElab fc env ts)
    = do pp <- getPPrint
         setPPrint (record { fullNamespace = True } pp)
         let res = "Ambiguous elaboration. Possible correct results:\n\t" ++
                   showSep "\n\t" !(traverse (pshow env) ts)
         setPPrint pp
         pure res
perror (AmbiguousSearch fc env ts)
    = pure $ "Multiple solutions found in search. Possible correct results:\n\t" ++
           showSep "\n\t" !(traverse (pshowNoNorm env) ts)
perror (AmbiguityTooDeep fc n ns)
    = pure $ "Maximum ambiguity depth exceeded in "  ++ show !(getFullName n)
             ++ ": " ++ showSep " --> " (map show !(traverse getFullName ns))
perror (AllFailed ts)
    = case allUndefined ts of
           Just e => perror e
           _ => pure $ "Sorry, I can't find any elaboration which works. All errors:\n" ++
                     showSep "\n" !(traverse pAlterror ts)
  where
    pAlterror : (Maybe Name, Error) -> Core String
    pAlterror (Just n, err)
       = pure $ "If " ++ show !(getFullName n) ++ ": " ++ !(perror err) ++ "\n"
    pAlterror (Nothing, err)
       = pure $ "Possible error:\n\t" ++ !(perror err)

    allUndefined : List (Maybe Name, Error) -> Maybe Error
    allUndefined [] = Nothing
    allUndefined [(_, UndefinedName loc e)] = Just (UndefinedName loc e)
    allUndefined ((_, UndefinedName _ e) :: es) = allUndefined es
    allUndefined _ = Nothing
perror (RecordTypeNeeded _ _)
    = pure "Can't infer type for this record update"
perror (NotRecordField fc fld Nothing)
    = pure $ fld ++ " is not part of a record type"
perror (NotRecordField fc fld (Just ty))
    = pure $ "Record type " ++ show ty ++ " has no field " ++ fld
perror (NotRecordType fc ty)
    = pure $ show ty ++ " is not a record type"
perror (IncompatibleFieldUpdate fc flds)
    = pure $ "Field update " ++ showSep "->" flds ++
             " not compatible with other updates"
perror (InvalidImplicits _ env [Just n] tm)
    = pure $ show n ++ " is not a valid implicit argument in " ++ !(pshow env tm)
perror (InvalidImplicits _ env ns tm)
    = pure $ showSep ", " (map show ns) ++
             " are not valid implicit arguments in " ++ !(pshow env tm)
perror (TryWithImplicits _ env imps)
    = pure $ "Need to bind implicits "
             ++ showSep ", " !(traverse (tshow env) imps)
  where
    tshow : {vars : _} ->
            Env Term vars -> (Name, Term vars) -> Core String
    tshow env (n, ty) = pure $ show n ++ " : " ++ !(pshow env ty)
perror (BadUnboundImplicit _ env n ty)
    = pure $ "Can't bind name " ++ nameRoot n ++ " with type " ++ !(pshow env ty)
               ++ " here. Try binding explicitly."
perror (CantSolveGoal _ env g)
    = let (_ ** (env', g')) = dropPis env g in
          pure $ "Can't find an implementation for " ++ !(pshow env' g')
  where
    -- For display, we don't want to see the full top level type; just the
    -- return type
    dropPis : {vars : _} ->
              Env Term vars -> Term vars ->
              (ns ** (Env Term ns, Term ns))
    dropPis env (Bind _ n b@(Pi _ _ _) sc) = dropPis (b :: env) sc
    dropPis env tm = (_ ** (env, tm))

perror (DeterminingArg _ n i env g)
    = pure $ "Can't find an implementation for " ++ !(pshow env g) ++ "\n" ++
             "since I can't infer a value for argument " ++ show n
perror (UnsolvedHoles hs)
    = pure $ "Unsolved holes:\n" ++ showHoles hs
  where
    showHoles : List (FC, Name) -> String
    showHoles [] = ""
    showHoles ((fc, n) :: hs) = show n ++ " introduced at " ++ show fc ++ "\n"
                                       ++ showHoles hs
perror (CantInferArgType _ env n h ty)
    = pure $ "Can't infer type for argument " ++ show n ++ "\n" ++
             "Got " ++ !(pshow env ty) ++ " with hole " ++ show h
perror (SolvedNamedHole _ env h tm)
    = pure $ "Named hole " ++ show h ++ " has been solved by unification\n"
              ++ "Result: " ++ !(pshow env tm)
perror (VisibilityError fc vx x vy y)
    = pure $ show vx ++ " " ++ sugarName !(toFullNames x) ++
             " cannot refer to " ++ show vy ++ " " ++ sugarName !(toFullNames y)
perror (NonLinearPattern _ n) = pure $ "Non linear pattern " ++ sugarName n
perror (BadPattern _ n) = pure $ "Pattern not allowed here: " ++ show n
perror (NoDeclaration _ n) = pure $ "No type declaration for " ++ show n
perror (AlreadyDefined _ n) = pure $ show n ++ " is already defined"
perror (NotFunctionType _ env tm)
    = pure $ !(pshow env tm) ++ " is not a function type"
perror (RewriteNoChange _ env rule ty)
    = pure $ "Rewriting by " ++ !(pshow env rule) ++
             " did not change type " ++ !(pshow env ty)
perror (NotRewriteRule fc env rule)
    = pure $ !(pshow env rule) ++ " is not a rewrite rule type"
perror (CaseCompile _ n DifferingArgNumbers)
    = pure $ "Patterns for " ++ !(prettyName n) ++ " have differing numbers of arguments"
perror (CaseCompile _ n DifferingTypes)
    = pure $ "Patterns for " ++ !(prettyName n) ++ " require matching on different types"
perror (CaseCompile _ n UnknownType)
    = pure $ "Can't infer type to match in " ++ !(prettyName n)
perror (CaseCompile fc n (NotFullyApplied cn))
    = pure $ "Constructor " ++ show !(toFullNames cn) ++ " is not fully applied"
perror (CaseCompile fc n (MatchErased (_ ** (env, tm))))
    = pure $ "Attempt to match on erased argument " ++ !(pshow env tm) ++
             " in " ++ !(prettyName n)
perror (BadDotPattern _ env reason x y)
    = pure $ "Can't match on " ++ !(pshow env x) ++
           " (" ++ show reason ++ ")"
perror (MatchTooSpecific _ env tm)
    = pure $ "Can't match on " ++ !(pshow env tm) ++
             " as it has a polymorphic type"
perror (BadImplicit _ str)
    = pure $ "Can't infer type for unbound implicit name " ++ str ++ "\n" ++
             "Try making it a bound implicit."
perror (BadRunElab _ env script)
    = pure $ "Bad elaborator script " ++ !(pshow env script)
perror (GenericMsg _ str) = pure str
perror (TTCError msg) = pure $ "Error in TTC file: " ++ show msg
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
           Warning -> Core String
pwarning (UnreachableClause fc env tm)
    = pure $ "Warning: unreachable clause: " ++ !(pshow env tm)

export
display : {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          Error -> Core String
display err
    = pure $ maybe "" (\f => show f ++ ":") (getErrorLoc err) ++
                   !(perror err)

export
displayWarning : {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 Warning -> Core String
displayWarning w
    = pure $ maybe "" (\f => show f ++ ":") (getWarningLoc w) ++
                   !(pwarning w)
