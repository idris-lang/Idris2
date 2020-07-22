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
import Idris.Pretty

import Parser.Source

import Data.List
import Data.List.Extra
import Data.Maybe
import Data.Stream
import Data.Strings
import Data.String.Extra
import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Util
import System.File

%default covering

pshow : {vars : _} ->
        {auto c : Ref Ctxt Defs} ->
        {auto s : Ref Syn SyntaxInfo} ->
        Env Term vars -> Term vars -> Core (Doc IdrisAnn)
pshow env tm
    = do defs <- get Ctxt
         itm <- resugar env !(normaliseHoles defs env tm)
         pure (prettyTerm itm)

pshowNoNorm : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Env Term vars -> Term vars -> Core (Doc IdrisAnn)
pshowNoNorm env tm
    = do defs <- get Ctxt
         itm <- resugar env tm
         pure (prettyTerm itm)

ploc : {auto o : Ref ROpts REPLOpts} ->
       FC -> Core (Doc IdrisAnn)
ploc EmptyFC = pure emptyDoc
ploc (MkFC _ s e) = do
    let sr = fromInteger $ cast $ fst s
    let sc = fromInteger $ cast $ snd s
    let er = fromInteger $ cast $ fst e
    let ec = fromInteger $ cast $ snd e
    let nsize = length $ show (er + 1)
    source <- lines <$> getCurrentElabSource
    if sr == er
       then do
         let line = maybe emptyDoc pretty (elemAt source sr)
         let emph = spaces (cast sc) <+> pretty (Extra.replicate (ec `minus` sc) '^')
         pure $ space <+> pretty (sr + 1) <++> pipe <++> align (vsep [line, emph])
       else pure $ vsep (addLineNumbers nsize sr (pretty <$> extractRange sr (Prelude.min er (sr + 5)) source))
  where
    extractRange : Nat -> Nat -> List String -> List String
    extractRange s e xs = take ((e `minus` s) + 1) (drop s xs)
    pad : Nat -> String -> String
    pad size s = replicate (size `minus` length s) '0' ++ s
    addLineNumbers : Nat -> Nat -> List (Doc IdrisAnn) -> List (Doc IdrisAnn)
    addLineNumbers size st xs =
      snd $ foldl (\(i, s), l => (S i, snoc s (space <+> pretty (pad size $ show $ i + 1) <++> pipe <++> l))) (st, []) xs

export
perror : {auto c : Ref Ctxt Defs} ->
         {auto s : Ref Syn SyntaxInfo} ->
         {auto o : Ref ROpts REPLOpts} ->
         Error -> Core (Doc IdrisAnn)
perror (Fatal err) = perror err
perror (CantConvert fc env l r)
    = pure $ vsep [ reflow "Mismatch between" <+> colon
                  , indent 4 !(pshow env l)
                  , pretty "and"
                  , indent 4 !(pshow env r)
                  , pretty "at" <+> colon
                  , !(ploc fc)
                  ]
perror (CantSolveEq fc env l r)
    = pure $ vsep [ reflow "Can't solve constraint between" <+> colon
                  , indent 4 !(pshow env l)
                  , pretty "and"
                  , indent 4 !(pshow env r)
                  , pretty "at" <+> colon
                  , !(ploc fc)
                  ]
perror (PatternVariableUnifies fc env n tm)
    = pure $ vsep [ reflow "Pattern variable" <++> pretty (showPVar n) <++> reflow "unifies with" <+> colon
                  , indent 4 !(pshow env tm)
                  , pretty "at" <+> colon
                  , !(ploc fc)
                  ]
  where
    showPVar : Name -> String
    showPVar (PV n _) = showPVar n
    showPVar n = show n
perror (CyclicMeta fc env n tm)
    = pure $ reflow "Cycle detected in solution of metavariable" <++> pretty !(prettyName n) <++> equals
        <++> !(pshow env tm) <++> pretty "at" <+> colon <+> line
        <+> !(ploc fc)
perror (WhenUnifying _ env x y err)
    = pure $ reflow "When unifying" <++> !(pshow env x) <++> pretty "and"
        <++> !(pshow env y) <+> line
        <+> !(perror err)
perror (ValidCase fc env (Left tm))
    = pure $ !(pshow env tm) <++> reflow "is not a valid impossible case at"
        <+> colon <+> line <+> !(ploc fc)
perror (ValidCase _ env (Right err))
    = pure $ reflow "Impossible pattern gives an error" <+> colon <+> line <+> !(perror err)
perror (UndefinedName fc x)
    = pure $ reflow "Undefined name" <++> pretty (show x)
        <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (InvisibleName fc n (Just ns))
    = pure $ pretty "Name" <++> pretty (show n) <++> reflow "is inaccessible since"
        <++> concatWith (surround dot) (pretty <$> reverse ns) <++> reflow "is not explicitly imported at"
        <+> colon <+> line <+> !(ploc fc)
perror (InvisibleName fc x Nothing)
    = pure $ pretty "Name" <++> pretty (show x) <++> reflow "is private at" <+> colon <+> line <+> !(ploc fc)
perror (BadTypeConType fc n)
    = pure $ reflow "Return type of" <++> pretty (show n) <++> reflow "must be Type at" <+> colon <+> line <+> !(ploc fc)
perror (BadDataConType fc n fam)
    = pure $ reflow "Return type of" <++> pretty (show n) <++> reflow "must be in"
        <++> pretty (show !(toFullNames fam)) <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (NotCovering fc n IsCovering)
    = pure $ reflow "Internal error" <++> parens (reflow "Coverage of" <++> pretty (show n))
perror (NotCovering fc n (MissingCases cs))
    = pure $ vsep [ pretty !(prettyName n) <++> reflow "is not covering at" <+> colon
                  , !(ploc fc)
                  , reflow "Missing cases" <+> colon
                  , indent 4 (vsep !(traverse (pshow []) cs))
                  ]
perror (NotCovering fc n (NonCoveringCall ns))
    = pure $ vsep [ pretty !(prettyName n) <++> reflow "is not covering at" <+> colon
                  , !(ploc fc)
                  , reflow "Calls non covering function" <+>
                      case ns of
                           [fn] => space <+> pretty (show fn)
                           _ => pretty 's' <+> colon <++> concatWith (surround (comma <+> space)) (pretty . show <$> ns)
                  ]
perror (NotTotal fc n r)
    = pure $ vsep [ pretty !(prettyName n) <++> reflow "is not total" <+> colon
                  , pretty (show r)
                  , pretty "at" <+> colon
                  , !(ploc fc)
                  ]
perror (LinearUsed fc count n)
    = pure $ reflow "There are" <++> pretty (show count) <++> reflow "uses of linear name" <++> pretty (sugarName n)
        <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (LinearMisuse fc n exp ctx)
    = if isErased exp
         then pure $ pretty (show n) <++> reflow "is not accessible in this context at" <+> colon <+> line <+> !(ploc fc)
         else pure $ reflow "Trying to use" <++> prettyRig exp <++> pretty "name" <++> pretty (sugarName n) <++>
                 pretty "in" <++> prettyRel ctx <++> pretty "context at" <+> colon <+> line <+> !(ploc fc)
  where
    prettyRig : RigCount -> Doc ann
    prettyRig = elimSemi (pretty "irrelevant")
                         (pretty "linear")
                         (const $ pretty "unrestricted")

    prettyRel : RigCount -> Doc ann
    prettyRel = elimSemi (pretty "irrelevant")
                         (pretty "relevant")
                         (const $ pretty "non-linear")
perror (BorrowPartial fc env tm arg)
    = pure $ !(pshow env tm) <++>
             reflow "borrows argument" <++> !(pshow env arg) <++>
             reflow "so must be fully applied at" <+> colon <+> line <+> !(ploc fc)
perror (BorrowPartialType fc env tm)
    = pure $ !(pshow env tm) <++>
        reflow "borrows, so must return a concrete type at" <+> colon <+> line <+> !(ploc fc)
perror (AmbiguousName fc ns)
    = pure $ pretty "Ambiguous name" <++> pretty (show ns) <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (AmbiguousElab fc env ts)
    = do pp <- getPPrint
         setPPrint (record { fullNamespace = True } pp)
         let res = vsep [ reflow "Ambiguous elaboration at" <+> colon
                        , !(ploc fc)
                        , reflow "Possible correct results" <+> colon
                        , indent 4 (vsep !(traverse (pshow env) ts))
                        ]
         setPPrint pp
         pure res
perror (AmbiguousSearch fc env tgt ts)
    = pure $ vsep [ reflow "Multiple solutions found in search of" <+> colon
                  , indent 4 !(pshowNoNorm env tgt)
                  , pretty "at" <+> colon
                  , !(ploc fc)
                  , reflow "Possible correct results" <+> colon
                  , indent 4 (vsep !(traverse (pshowNoNorm env) ts))
                  ]
perror (AmbiguityTooDeep fc n ns)
    = pure $ reflow "Maximum ambiguity depth exceeded in" <++> pretty (show !(getFullName n))
        <+> colon <++> concatWith (surround (pretty " --> ")) (pretty . show <$> !(traverse getFullName ns))
        <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (AllFailed ts)
    = case allUndefined ts of
           Just e => perror e
           _ => pure $ reflow "Sorry, I can't find any elaboration which works. All errors" <+> colon <+> line
                  <+> vsep !(traverse pAlterror ts)
  where
    pAlterror : (Maybe Name, Error) -> Core (Doc IdrisAnn)
    pAlterror (Just n, err)
       = pure $ pretty "If" <++> pretty (show !(aliasName !(getFullName n))) <+> colon <++> !(perror err) <+> line
    pAlterror (Nothing, err)
       = pure $ reflow "Possible error" <+> colon <+> line <+> indent 4 !(perror err)

    allUndefined : List (Maybe Name, Error) -> Maybe Error
    allUndefined [] = Nothing
    allUndefined [(_, UndefinedName loc e)] = Just (UndefinedName loc e)
    allUndefined ((_, UndefinedName _ e) :: es) = allUndefined es
    allUndefined _ = Nothing
perror (RecordTypeNeeded fc _)
    = pure $ reflow "Can't infer type for this record update at" <+> colon <+> line <+> !(ploc fc)
perror (NotRecordField fc fld Nothing)
    = pure $ pretty fld <++> reflow "is not part of a record type at" <+> colon <+> line <+> !(ploc fc)
perror (NotRecordField fc fld (Just ty))
    = pure $ reflow "Record type" <++> pretty (show !(getFullName ty)) <++> reflow "has no field" <++> pretty fld
        <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (NotRecordType fc ty)
    = pure $ pretty (show !(getFullName ty)) <++> reflow "is not a record type at" <+> colon <+> line <+> !(ploc fc)
perror (IncompatibleFieldUpdate fc flds)
    = pure $ reflow "Field update" <++> concatWith (surround (pretty "->")) (pretty <$> flds)
             <++> reflow "not compatible with other updates at" <+> colon <+> line <+> !(ploc fc)
perror (InvalidImplicits fc env [Just n] tm)
    = pure $ pretty (show n) <++> reflow "is not a valid implicit argument in" <++> !(pshow env tm)
        <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (InvalidImplicits fc env ns tm)
    = pure $ concatWith (surround (comma <+> space)) (pretty . show <$> ns)
        <++> reflow "are not valid implicit arguments in" <++> !(pshow env tm)
        <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (TryWithImplicits fc env imps)
    = pure $ reflow "Need to bind implicits"
        <++> concatWith (surround (comma <+> space)) !(traverse (tshow env) imps)
        <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
  where
    tshow : {vars : _} ->
            Env Term vars -> (Name, Term vars) -> Core (Doc IdrisAnn)
    tshow env (n, ty) = pure $ pretty (show n) <++> colon <++> !(pshow env ty)
perror (BadUnboundImplicit fc env n ty)
    = pure $ reflow "Can't bind name" <++> pretty (nameRoot n) <++> reflow "with type" <++> !(pshow env ty)
        <++> reflow "here at" <+> colon <+> line <+> !(ploc fc) <+> line <+> reflow "Try binding explicitly."
perror (CantSolveGoal fc env g)
    = let (_ ** (env', g')) = dropEnv env g in
          pure $ reflow "Can't find an implementation for" <++> !(pshow env' g')
            <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
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
    = pure $ reflow "Can't find an implementation for" <++> !(pshow env g) <+> line
        <+> reflow "since I can't infer a value for argument" <++> pretty (show n)
        <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (UnsolvedHoles hs)
    = pure $ reflow "Unsolved holes" <+> colon <+> line <+> prettyHoles hs
  where
    prettyHoles : List (FC, Name) -> Doc IdrisAnn
    prettyHoles [] = emptyDoc
    prettyHoles ((fc, n) :: hs)
        = pretty (show n) <++> reflow "introduced at" <++> pretty (show fc) <+> line <+> prettyHoles hs
perror (CantInferArgType fc env n h ty)
    = pure $ reflow "Can't infer type for argument" <++> pretty (show n) <+> line
        <+> pretty "Got" <++> !(pshow env ty) <++> reflow "with hole" <++> pretty (show h)
        <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (SolvedNamedHole fc env h tm)
    = pure $ reflow "Named hole" <++> pretty (show h) <++> reflow "has been solved by unification" <+> line
        <+> pretty "Result" <+> colon <++> !(pshow env tm)
        <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (VisibilityError fc vx x vy y)
    = pure $ pretty (show vx) <++> pretty (sugarName !(toFullNames x))
        <++> reflow "cannot refer to" <++> pretty (show vy) <++> pretty (sugarName !(toFullNames y))
        <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (NonLinearPattern fc n)
    = pure $ reflow "Non linear pattern" <++> pretty (sugarName n) <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (BadPattern fc n)
    = pure $ reflow "Pattern not allowed here" <+> colon <++> pretty (show n) <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (NoDeclaration fc n)
    = pure $ reflow "No type declaration for" <++> pretty (show n) <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (AlreadyDefined fc n) = pure $ pretty (show n) <++> reflow "is already defined"
perror (NotFunctionType fc env tm)
    = pure $ !(pshow env tm) <++> reflow "is not a function type at" <+> colon <+> line <+> !(ploc fc)
perror (RewriteNoChange fc env rule ty)
    = pure $ reflow "Rewriting by" <++> !(pshow env rule)
        <++> reflow "did not change type" <++> !(pshow env ty)
        <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (NotRewriteRule fc env rule)
    = pure $ !(pshow env rule) <++> reflow "is not a rewrite rule type at" <+> colon <+> line <+> !(ploc fc)
perror (CaseCompile fc n DifferingArgNumbers)
    = pure $ reflow "Patterns for" <++> pretty !(prettyName n) <++> reflow "have differing numbers of arguments at"
        <+> colon <+> line <+> !(ploc fc)
perror (CaseCompile fc n DifferingTypes)
    = pure $ reflow "Patterns for" <++> pretty !(prettyName n) <++> reflow "require matching on different types at"
        <+> colon <+> line <+> !(ploc fc)
perror (CaseCompile fc n UnknownType)
    = pure $ reflow "Can't infer type to match in" <++> pretty !(prettyName n) <++> pretty "at"
        <+> colon <+> line <+> !(ploc fc)
perror (CaseCompile fc n (NotFullyApplied cn))
    = pure $ pretty "Constructor" <++> pretty (show !(toFullNames cn)) <++> reflow "is not fully applied at"
         <+> colon <+> line <+> !(ploc fc)
perror (CaseCompile fc n (MatchErased (_ ** (env, tm))))
    = pure $ reflow "Attempt to match on erased argument" <++> !(pshow env tm) <++> pretty "in"
        <++> pretty !(prettyName n) <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (BadDotPattern fc env reason x y)
    = pure $ reflow "Can't match on" <++> !(pshow env x)
        <++> parens (pretty (show reason)) <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (MatchTooSpecific fc env tm)
    = pure $ reflow "Can't match on" <++> !(pshow env tm)
        <++> reflow "as it has a polymorphic type at" <+> colon <+> line <+> !(ploc fc)
perror (BadImplicit fc str)
    = pure $ reflow "Can't infer type for unbound implicit name" <++> pretty str <++> pretty "at" <+> colon
        <+> line <+> !(ploc fc) <+> line <+> reflow "Try making it a bound implicit."
perror (BadRunElab fc env script)
    = pure $ reflow "Bad elaborator script" <++> !(pshow env script)
        <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (GenericMsg fc str) = pure $ pretty str <++> pretty "at" <+> colon <+> line <+> !(ploc fc)
perror (TTCError msg)
    = pure $ reflow "Error in TTC file" <+> colon <++> pretty (show msg)
        <++> parens (pretty "the most likely case is that the ./build directory in your current project contains files from a previous build of idris2 or the idris2 executable is from a different build than the installed .ttc files")
perror (FileErr fname err)
    = pure $ reflow "File error in" <++> pretty fname <++> colon <++> pretty (show err)
perror (ParseFail _ err)
    = pure $ pretty (show err)
perror (ModuleNotFound _ ns)
    = pure $ concatWith (surround dot) (pretty <$> reverse ns) <++> reflow "not found"
perror (CyclicImports ns)
    = pure $ reflow "Module imports form a cycle" <+> colon <++> concatWith (surround (pretty " -> ")) (prettyMod <$> ns)
  where
    prettyMod : List String -> Doc IdrisAnn
    prettyMod ns = concatWith (surround dot) (pretty <$> reverse ns)
perror ForceNeeded = pure $ reflow "Internal error when resolving implicit laziness"
perror (InternalError str) = pure $ reflow "INTERNAL ERROR" <+> colon <++> pretty str
perror (UserError str) = pure $ pretty "Error" <+> colon <++> pretty str

perror (InType fc n err)
    = pure $ reflow "While processing type of" <++> pretty !(prettyName n)
        <++> pretty "at" <++> pretty (show fc) <+> colon <+> line <+> !(perror err)
perror (InCon fc n err)
    = pure $ reflow "While processing constructor" <++> pretty !(prettyName n)
        <++> pretty "at" <++> pretty (show fc) <+> colon <+> line <+> !(perror err)
perror (InLHS fc n err)
    = pure $ reflow "While processing left hand side of" <++> pretty !(prettyName n)
        <++> pretty "at" <++> pretty (show fc) <+> colon <+> line <+> !(perror err)
perror (InRHS fc n err)
    = pure $ reflow "While processing right hand side of" <++> pretty !(prettyName n)
        <++> pretty "at" <++> pretty (show fc) <+> colon <+> line <+> !(perror err)

export
pwarning : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           Warning -> Core (Doc IdrisAnn)
pwarning (UnreachableClause fc env tm)
    = pure $ annotate Warning (pretty "Warning" <+> colon)
        <++> pretty "unreachable clause" <+> colon
        <++> !(pshow env tm)

prettyMaybeLoc : Maybe FC -> Doc IdrisAnn
prettyMaybeLoc Nothing = emptyDoc
prettyMaybeLoc (Just fc) = annotate FileCtxt (pretty fc) <+> colon

export
display : {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto o : Ref ROpts REPLOpts} ->
          Error -> Core (Doc IdrisAnn)
display err
    = pure $ prettyMaybeLoc (getErrorLoc err) <+> !(perror err)

export
displayWarning : {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 Warning -> Core (Doc IdrisAnn)
displayWarning w
    = pure $ prettyMaybeLoc (getWarningLoc w) <+> !(pwarning w)
