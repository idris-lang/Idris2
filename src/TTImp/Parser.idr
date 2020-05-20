module TTImp.Parser

import Core.Context
import Core.Core
import Core.Env
import Core.TT
import Parser.Source
import TTImp.TTImp

import public Text.Parser
import        Data.List
import        Data.List.Views
import        Data.Strings

topDecl : FileName -> IndentInfo -> SourceRule ImpDecl
-- All the clauses get parsed as one-clause definitions. Collect any
-- neighbouring clauses with the same function name into one definition.
export
collectDefs : List ImpDecl -> List ImpDecl

%hide Prelude.(>>=)
%hide Core.Core.(>>=)
%hide Prelude.pure
%hide Core.Core.pure

%hide Lexer.Core.(<|>)
%hide Prelude.(<|>)

atom : FileName -> SourceRule RawImp
atom fname
    = do start <- location
         x <- constant
         end <- location
         pure (IPrimVal (MkFC fname start end) x)
  <|> do start <- location
         exactIdent "Type"
         end <- location
         pure (IType (MkFC fname start end))
  <|> do start <- location
         symbol "_"
         end <- location
         pure (Implicit (MkFC fname start end) True)
  <|> do start <- location
         symbol "?"
         end <- location
         pure (Implicit (MkFC fname start end) False)
  <|> do start <- location
         pragma "search"
         end <- location
         pure (ISearch (MkFC fname start end) 1000)
  <|> do start <- location
         x <- name
         end <- location
         pure (IVar (MkFC fname start end) x)
  <|> do start <- location
         symbol "$"
         x <- unqualifiedName
         end <- location
         pure (IBindVar (MkFC fname start end) x)
  <|> do start <- location
         x <- holeName
         end <- location
         pure (IHole (MkFC fname start end) x)

visOption : SourceRule Visibility
visOption
    = do keyword "public"
         keyword "export"
         pure Public
  <|> do keyword "export"
         pure Export
  <|> do keyword "private"
         pure Private

visibility : SourceEmptyRule Visibility
visibility
    = visOption
  <|> pure Private

totalityOpt : SourceRule TotalReq
totalityOpt
    = do keyword "partial"
         pure PartialOK
  <|> do keyword "total"
         pure Total
  <|> do keyword "covering"
         pure CoveringOnly

fnOpt : SourceRule FnOpt
fnOpt = do x <- totalityOpt
           pure $ Totality x

fnDirectOpt : SourceRule FnOpt
fnDirectOpt
    = do pragma "hint"
         pure (Hint True)
  <|> do pragma "chaser"
         pure (Hint False)
  <|> do pragma "globalhint"
         pure (GlobalHint True)
  <|> do pragma "defaulthint"
         pure (GlobalHint False)
  <|> do pragma "inline"
         pure Inline
  <|> do pragma "extern"
         pure ExternFn

visOpt : SourceRule (Either Visibility FnOpt)
visOpt
    = do vis <- visOption
         pure (Left vis)
  <|> do tot <- fnOpt
         pure (Right tot)
  <|> do opt <- fnDirectOpt
         pure (Right opt)

getVisibility : Maybe Visibility -> List (Either Visibility FnOpt) ->
               SourceEmptyRule Visibility
getVisibility Nothing [] = pure Private
getVisibility (Just vis) [] = pure vis
getVisibility Nothing (Left x :: xs) = getVisibility (Just x) xs
getVisibility (Just vis) (Left x :: xs)
   = fatalError "Multiple visibility modifiers"
getVisibility v (_ :: xs) = getVisibility v xs

getRight : Either a b -> Maybe b
getRight (Left _) = Nothing
getRight (Right v) = Just v

bindSymbol : SourceRule (PiInfo RawImp)
bindSymbol
    = do symbol "->"
         pure Explicit
  <|> do symbol "=>"
         pure AutoImplicit

mutual
  appExpr : FileName -> IndentInfo -> SourceRule RawImp
  appExpr fname indents
      = case_ fname indents
    <|> lazy fname indents
    <|> do start <- location
           f <- simpleExpr fname indents
           args <- many (argExpr fname indents)
           end <- location
           pure (applyExpImp start end f args)
    where
      applyExpImp : FilePos -> FilePos ->
                    RawImp -> List (Either RawImp (Maybe Name, RawImp)) ->
                    RawImp
      applyExpImp start end f [] = f
      applyExpImp start end f (Left exp :: args)
          = applyExpImp start end (IApp (MkFC fname start end) f exp) args
      applyExpImp start end f (Right (n, imp) :: args)
          = applyExpImp start end (IImplicitApp (MkFC fname start end) f n imp) args

  argExpr : FileName -> IndentInfo ->
            SourceRule (Either RawImp (Maybe Name, RawImp))
  argExpr fname indents
      = do continue indents
           arg <- simpleExpr fname indents
           pure (Left arg)
    <|> do continue indents
           arg <- implicitArg fname indents
           pure (Right arg)

  implicitArg : FileName -> IndentInfo -> SourceRule (Maybe Name, RawImp)
  implicitArg fname indents
      = do start <- location
           symbol "{"
           x <- unqualifiedName
           (do symbol "="
               commit
               tm <- expr fname indents
               symbol "}"
               pure (Just (UN x), tm))
             <|> (do symbol "}"
                     end <- location
                     pure (Just (UN x), IVar (MkFC fname start end) (UN x)))
    <|> do symbol "@{"
           commit
           tm <- expr fname indents
           symbol "}"
           pure (Nothing, tm)

  as : FileName -> IndentInfo -> SourceRule RawImp
  as fname indents
      = do start <- location
           x <- unqualifiedName
           symbol "@"
           pat <- simpleExpr fname indents
           end <- location
           pure (IAs (MkFC fname start end) UseRight (UN x) pat)

  simpleExpr : FileName -> IndentInfo -> SourceRule RawImp
  simpleExpr fname indents
      = as fname indents
    <|> atom fname
    <|> binder fname indents
    <|> rewrite_ fname indents
    <|> record_ fname indents
    <|> do symbol "("
           e <- expr fname indents
           symbol ")"
           pure e

  multiplicity : SourceEmptyRule (Maybe Integer)
  multiplicity
      = do c <- intLit
           pure (Just c)
    <|> pure Nothing

  getMult : Maybe Integer -> SourceEmptyRule RigCount
  getMult (Just 0) = pure erased
  getMult (Just 1) = pure linear
  getMult Nothing = pure top
  getMult _ = fatalError "Invalid multiplicity (must be 0 or 1)"

  pibindAll : FC -> PiInfo RawImp -> List (RigCount, Maybe Name, RawImp) ->
              RawImp -> RawImp
  pibindAll fc p [] scope = scope
  pibindAll fc p ((rig, n, ty) :: rest) scope
           = IPi fc rig p n ty (pibindAll fc p rest scope)

  bindList : FileName -> FilePos -> IndentInfo ->
             SourceRule (List (RigCount, Name, RawImp))
  bindList fname start indents
      = sepBy1 (symbol ",")
               (do rigc <- multiplicity
                   n <- unqualifiedName
                   end <- location
                   ty <- option
                            (Implicit (MkFC fname start end) False)
                            (do symbol ":"
                                appExpr fname indents)
                   rig <- getMult rigc
                   pure (rig, UN n, ty))


  pibindListName : FileName -> FilePos -> IndentInfo ->
                   SourceRule (List (RigCount, Name, RawImp))
  pibindListName fname start indents
       = do rigc <- multiplicity
            ns <- sepBy1 (symbol ",") unqualifiedName
            symbol ":"
            ty <- expr fname indents
            atEnd indents
            rig <- getMult rigc
            pure (map (\n => (rig, UN n, ty)) ns)
     <|> sepBy1 (symbol ",")
                (do rigc <- multiplicity
                    n <- name
                    symbol ":"
                    ty <- expr fname indents
                    rig <- getMult rigc
                    pure (rig, n, ty))

  pibindList : FileName -> FilePos -> IndentInfo ->
               SourceRule (List (RigCount, Maybe Name, RawImp))
  pibindList fname start indents
    = do params <- pibindListName fname start indents
         pure $ map (\(rig, n, ty) => (rig, Just n, ty)) params


  autoImplicitPi : FileName -> IndentInfo -> SourceRule RawImp
  autoImplicitPi fname indents
      = do start <- location
           symbol "{"
           keyword "auto"
           commit
           binders <- pibindList fname start indents
           symbol "}"
           symbol "->"
           scope <- typeExpr fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) AutoImplicit binders scope)

  forall_ : FileName -> IndentInfo -> SourceRule RawImp
  forall_ fname indents
      = do start <- location
           keyword "forall"
           commit
           nstart <- location
           ns <- sepBy1 (symbol ",") unqualifiedName
           nend <- location
           let nfc = MkFC fname nstart nend
           let binders = map (\n => (erased {a=RigCount}, Just (UN n), Implicit nfc False)) ns
           symbol "."
           scope <- typeExpr fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) Implicit binders scope)

  implicitPi : FileName -> IndentInfo -> SourceRule RawImp
  implicitPi fname indents
      = do start <- location
           symbol "{"
           binders <- pibindList fname start indents
           symbol "}"
           symbol "->"
           scope <- typeExpr fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) Implicit binders scope)

  explicitPi : FileName -> IndentInfo -> SourceRule RawImp
  explicitPi fname indents
      = do start <- location
           symbol "("
           binders <- pibindList fname start indents
           symbol ")"
           exp <- bindSymbol
           scope <- typeExpr fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) exp binders scope)

  lam : FileName -> IndentInfo -> SourceRule RawImp
  lam fname indents
      = do start <- location
           symbol "\\"
           binders <- bindList fname start indents
           symbol "=>"
           mustContinue indents Nothing
           scope <- expr fname indents
           end <- location
           pure (bindAll (MkFC fname start end) binders scope)
     where
       bindAll : FC -> List (RigCount, Name, RawImp) -> RawImp -> RawImp
       bindAll fc [] scope = scope
       bindAll fc ((rig, n, ty) :: rest) scope
           = ILam fc rig Explicit (Just n) ty (bindAll fc rest scope)

  let_ : FileName -> IndentInfo -> SourceRule RawImp
  let_ fname indents
      = do start <- location
           keyword "let"
           rigc <- multiplicity
           rig <- getMult rigc
           n <- name
           symbol "="
           commit
           val <- expr fname indents
           continue indents
           keyword "in"
           scope <- typeExpr fname indents
           end <- location
           pure (let fc = MkFC fname start end in
                     ILet fc rig n (Implicit fc False) val scope)
    <|> do start <- location
           keyword "let"
           ds <- block (topDecl fname)
           continue indents
           keyword "in"
           scope <- typeExpr fname indents
           end <- location
           pure (ILocal (MkFC fname start end) (collectDefs ds) scope)

  case_ : FileName -> IndentInfo -> SourceRule RawImp
  case_ fname indents
      = do start <- location
           keyword "case"
           scr <- expr fname indents
           keyword "of"
           alts <- block (caseAlt fname)
           end <- location
           pure (let fc = MkFC fname start end in
                     ICase fc scr (Implicit fc False) alts)

  caseAlt : FileName -> IndentInfo -> SourceRule ImpClause
  caseAlt fname indents
      = do start <- location
           lhs <- appExpr fname indents
           caseRHS fname indents start lhs

  caseRHS : FileName -> IndentInfo -> (Int, Int) -> RawImp ->
            SourceRule ImpClause
  caseRHS fname indents start lhs
      = do symbol "=>"
           continue indents
           rhs <- expr fname indents
           atEnd indents
           end <- location
           pure (PatClause (MkFC fname start end) lhs rhs)
    <|> do keyword "impossible"
           atEnd indents
           end <- location
           pure (ImpossibleClause (MkFC fname start end) lhs)

  record_ : FileName -> IndentInfo -> SourceRule RawImp
  record_ fname indents
      = do start <- location
           keyword "record"
           symbol "{"
           commit
           fs <- sepBy1 (symbol ",") (field fname indents)
           symbol "}"
           sc <- expr fname indents
           end <- location
           pure (IUpdate (MkFC fname start end) fs sc)

  field : FileName -> IndentInfo -> SourceRule IFieldUpdate
  field fname indents
      = do path <- sepBy1 (symbol "->") unqualifiedName
           upd <- (do symbol "="; pure ISetField)
                      <|>
                  (do symbol "$="; pure ISetFieldApp)
           val <- appExpr fname indents
           pure (upd path val)

  rewrite_ : FileName -> IndentInfo -> SourceRule RawImp
  rewrite_ fname indents
      = do start <- location
           keyword "rewrite"
           rule <- expr fname indents
           keyword "in"
           tm <- expr fname indents
           end <- location
           pure (IRewrite (MkFC fname start end) rule tm)

  lazy : FileName -> IndentInfo -> SourceRule RawImp
  lazy fname indents
      = do start <- location
           exactIdent "Lazy"
           tm <- simpleExpr fname indents
           end <- location
           pure (IDelayed (MkFC fname start end) LLazy tm)
    <|> do start <- location
           exactIdent "Inf"
           tm <- simpleExpr fname indents
           end <- location
           pure (IDelayed (MkFC fname start end) LInf tm)
    <|> do start <- location
           exactIdent "Delay"
           tm <- simpleExpr fname indents
           end <- location
           pure (IDelay (MkFC fname start end) tm)
    <|> do start <- location
           exactIdent "Force"
           tm <- simpleExpr fname indents
           end <- location
           pure (IForce (MkFC fname start end) tm)


  binder : FileName -> IndentInfo -> SourceRule RawImp
  binder fname indents
      = autoImplicitPi fname indents
    <|> forall_ fname indents
    <|> implicitPi fname indents
    <|> explicitPi fname indents
    <|> lam fname indents
    <|> let_ fname indents

  typeExpr : FileName -> IndentInfo -> SourceRule RawImp
  typeExpr fname indents
      = do start <- location
           arg <- appExpr fname indents
           (do continue indents
               rest <- some (do exp <- bindSymbol
                                op <- appExpr fname indents
                                pure (exp, op))
               end <- location
               pure (mkPi start end arg rest))
             <|> pure arg
    where
      mkPi : FilePos -> FilePos -> RawImp -> List (PiInfo RawImp, RawImp) -> RawImp
      mkPi start end arg [] = arg
      mkPi start end arg ((exp, a) :: as)
            = IPi (MkFC fname start end) top exp Nothing arg
                  (mkPi start end a as)

  export
  expr : FileName -> IndentInfo -> SourceRule RawImp
  expr = typeExpr

tyDecl : FileName -> IndentInfo -> SourceRule ImpTy
tyDecl fname indents
    = do start <- location
         n <- name
         symbol ":"
         ty <- expr fname indents
         end <- location
         atEnd indents
         pure (MkImpTy (MkFC fname start end) n ty)

mutual
  parseRHS : (withArgs : Nat) ->
             FileName -> IndentInfo -> (Int, Int) -> RawImp ->
             SourceRule (Name, ImpClause)
  parseRHS withArgs fname indents start lhs
      = do symbol "="
           commit
           rhs <- expr fname indents
           atEnd indents
           end <- location
           let fc = MkFC fname start end
           pure (!(getFn lhs), PatClause fc lhs rhs)
    <|> do keyword "with"
           wstart <- location
           symbol "("
           wval <- expr fname indents
           symbol ")"
           ws <- nonEmptyBlock (clause (S withArgs) fname)
           end <- location
           let fc = MkFC fname start end
           pure (!(getFn lhs), WithClause fc lhs wval (map snd ws))

    <|> do keyword "impossible"
           atEnd indents
           end <- location
           let fc = MkFC fname start end
           pure (!(getFn lhs), ImpossibleClause fc lhs)
    where
      getFn : RawImp -> SourceEmptyRule Name
      getFn (IVar _ n) = pure n
      getFn (IApp _ f a) = getFn f
      getFn (IImplicitApp _ f _ a) = getFn f
      getFn _ = fail "Not a function application"

  ifThenElse : Bool -> Lazy t -> Lazy t -> t
  ifThenElse True t e = t
  ifThenElse False t e = e

  clause : Nat -> FileName -> IndentInfo -> SourceRule (Name, ImpClause)
  clause withArgs fname indents
      = do start <- location
           lhs <- expr fname indents
           extra <- many parseWithArg
           ifThenElse (withArgs /= length extra)
              (fatalError "Wrong number of 'with' arguments")
              (parseRHS withArgs fname indents start (applyArgs lhs extra))
    where
      applyArgs : RawImp -> List (FC, RawImp) -> RawImp
      applyArgs f [] = f
      applyArgs f ((fc, a) :: args) = applyArgs (IApp fc f a) args

      parseWithArg : SourceRule (FC, RawImp)
      parseWithArg
          = do symbol "|"
               start <- location
               tm <- expr fname indents
               end <- location
               pure (MkFC fname start end, tm)

definition : FileName -> IndentInfo -> SourceRule ImpDecl
definition fname indents
    = do start <- location
         nd <- clause 0 fname indents
         end <- location
         pure (IDef (MkFC fname start end) (fst nd) [snd nd])

dataOpt : SourceRule DataOpt
dataOpt
    = do exactIdent "noHints"
         pure NoHints
  <|> do exactIdent "uniqueSearch"
         pure UniqueSearch
  <|> do exactIdent "search"
         ns <- some name
         pure (SearchBy ns)

dataDecl : FileName -> IndentInfo -> SourceRule ImpData
dataDecl fname indents
    = do start <- location
         keyword "data"
         n <- name
         symbol ":"
         ty <- expr fname indents
         keyword "where"
         opts <- option [] (do symbol "["
                               dopts <- sepBy1 (symbol ",") dataOpt
                               symbol "]"
                               pure dopts)
         cs <- block (tyDecl fname)
         end <- location
         pure (MkImpData (MkFC fname start end) n ty opts cs)

recordParam : FileName -> IndentInfo -> SourceRule (List (Name, RigCount, PiInfo RawImp, RawImp))
recordParam fname indents
    = do symbol "("
         start <- location
         params <- pibindListName fname start indents
         symbol ")"
         pure $ map (\(c, n, tm) => (n, c, Explicit, tm)) params
  <|> do symbol "{"
         commit
         start <- location
         info <- the (SourceEmptyRule (PiInfo RawImp))
                 (pure  AutoImplicit <* keyword "auto"
              <|>(do
                  keyword "default"
                  t <- simpleExpr fname indents
                  pure $ DefImplicit t)
              <|> pure      Implicit)
         params <- pibindListName fname start indents
         symbol "}"
         pure $ map (\(c, n, tm) => (n, c, info, tm)) params
  <|> do start <- location
         n <- name
         end <- location
         pure [(n, top, Explicit, Implicit (MkFC fname start end) False)]

fieldDecl : FileName -> IndentInfo -> SourceRule (List IField)
fieldDecl fname indents
      = do symbol "{"
           commit
           fs <- fieldBody Implicit
           symbol "}"
           atEnd indents
           pure fs
    <|> do fs <- fieldBody Explicit
           atEnd indents
           pure fs
  where
    fieldBody : PiInfo RawImp -> SourceRule (List IField)
    fieldBody p
        = do start <- location
             ns <- sepBy1 (symbol ",") unqualifiedName
             symbol ":"
             ty <- expr fname indents
             end <- location
             pure (map (\n => MkIField (MkFC fname start end)
                                       linear p (UN n) ty) ns)

recordDecl : FileName -> IndentInfo -> SourceRule ImpDecl
recordDecl fname indents
    = do start <- location
         vis <- visibility
         col <- column
         keyword "record"
         commit
         n <- name
         paramss <- many (recordParam fname indents)
         let params = concat paramss
         keyword "where"
         exactIdent "constructor"
         dc <- name
         flds <- assert_total (blockAfter col (fieldDecl fname))
         end <- location
         pure (let fc = MkFC fname start end in
                   IRecord fc Nothing vis
                           (MkImpRecord fc n params dc (concat flds)))

namespaceDecl : SourceRule (List String)
namespaceDecl
    = do keyword "namespace"
         commit
         ns <- nsIdent
         pure ns

directive : FileName -> IndentInfo -> SourceRule ImpDecl
directive fname indents
    = do pragma "logging"
         commit
         lvl <- intLit
         atEnd indents
         pure (ILog (integerToNat lvl))
         {- Can't do IPragma due to lack of Ref Ctxt. Should we worry about this?
  <|> do pragma "pair"
         commit
         start <- location
         p <- name
         f <- name
         s <- name
         end <- location
         pure (let fc = MkFC fname start end in
                   IPragma (\nest, env => setPair {c} fc p f s))
  <|> do pragma "rewrite"
         commit
         start <- location
         eq <- name
         rw <- name
         end <- location
         pure (let fc = MkFC fname start end in
                   IPragma (\c, nest, env => setRewrite {c} fc eq rw))
    -}
-- Declared at the top
-- topDecl : FileName -> IndentInfo -> SourceRule ImpDecl
topDecl fname indents
    = do start <- location
         vis <- visibility
         dat <- dataDecl fname indents
         end <- location
         pure (IData (MkFC fname start end) vis dat)
  <|> do start <- location
         ns <- namespaceDecl
         ds <- assert_total (nonEmptyBlock (topDecl fname))
         end <- location
         pure (INamespace (MkFC fname start end) ns ds)
  <|> do start <- location
         visOpts <- many visOpt
         vis <- getVisibility Nothing visOpts
         let opts = mapMaybe getRight visOpts
         claim <- tyDecl fname indents
         end <- location
         pure (IClaim (MkFC fname start end) top vis opts claim)
  <|> recordDecl fname indents
  <|> directive fname indents
  <|> definition fname indents

-- Declared at the top
-- collectDefs : List ImpDecl -> List ImpDecl
collectDefs [] = []
collectDefs (IDef loc fn cs :: ds)
    = let (cs', rest) = spanMap (isClause fn) ds in
          IDef loc fn (cs ++ cs') :: assert_total (collectDefs rest)
  where
    spanMap : (a -> Maybe (List b)) -> List a -> (List b, List a)
    spanMap f [] = ([], [])
    spanMap f (x :: xs) = case f x of
                               Nothing => ([], x :: xs)
                               Just y => case spanMap f xs of
                                              (ys, zs) => (y ++ ys, zs)

    isClause : Name -> ImpDecl -> Maybe (List ImpClause)
    isClause n (IDef _ n' cs)
        = if n == n' then Just cs else Nothing
    isClause n _ = Nothing
collectDefs (INamespace loc ns nds :: ds)
    = INamespace loc ns (collectDefs nds) :: collectDefs ds
collectDefs (d :: ds)
    = d :: collectDefs ds

-- full programs
export
prog : FileName -> SourceRule (List ImpDecl)
prog fname
    = do ds <- nonEmptyBlock (topDecl fname)
         pure (collectDefs ds)

-- TTImp REPL commands
export
command : SourceRule ImpREPL
command
    = do symbol ":"; exactIdent "t"
         tm <- expr "(repl)" init
         pure (Check tm)
  <|> do symbol ":"; exactIdent "s"
         n <- name
         pure (ProofSearch n)
  <|> do symbol ":"; exactIdent "es"
         n <- name
         pure (ExprSearch n)
  <|> do symbol ":"; exactIdent "gd"
         l <- intLit
         n <- name
         pure (GenerateDef (fromInteger l) n)
  <|> do symbol ":"; exactIdent "missing"
         n <- name
         pure (Missing n)
  <|> do symbol ":"; keyword "total"
         n <- name
         pure (CheckTotal n)
  <|> do symbol ":"; exactIdent "di"
         n <- name
         pure (DebugInfo n)
  <|> do symbol ":"; exactIdent "q"
         pure Quit
  <|> do tm <- expr "(repl)" init
         pure (Eval tm)
