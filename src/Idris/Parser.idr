module Idris.Parser

import        Core.Options
import        Idris.Syntax
import public Parser.Source
import        Parser.Lexer.Source
import        TTImp.TTImp

import public Text.Parser
import        Data.List
import        Data.List.Views
import        Data.Maybe
import        Data.Strings

%default covering

-- Forward declare since they're used in the parser
topDecl : FileName -> IndentInfo -> Rule (List PDecl)
collectDefs : List PDecl -> List PDecl

-- Some context for the parser
public export
record ParseOpts where
  constructor MkParseOpts
  eqOK : Bool -- = operator is parseable
  withOK : Bool -- = with applications are parseable

peq : ParseOpts -> ParseOpts
peq = record { eqOK = True }

pnoeq : ParseOpts -> ParseOpts
pnoeq = record { eqOK = False }

export
pdef : ParseOpts
pdef = MkParseOpts True True

pnowith : ParseOpts
pnowith = MkParseOpts True False

export
plhs : ParseOpts
plhs = MkParseOpts False False

%hide Prelude.(>>=)
%hide Core.Core.(>>=)
%hide Prelude.pure
%hide Core.Core.pure

atom : FileName -> Rule PTerm
atom fname
    = do (start, end) <- position
         exactIdent "Type"
         pure (PType (MkFC fname start end))
  <|> do (start, end) <- position
         x <- name
         pure (PRef (MkFC fname start end) x)
  <|> do (start, end) <- position
         x <- constant
         pure (PPrimVal (MkFC fname start end) x)
  <|> do (start, end) <- position
         symbol "_"
         pure (PImplicit (MkFC fname start end))
  <|> do (start, end) <- position
         symbol "?"
         pure (PInfer (MkFC fname start end))
  <|> do (start, end) <- position
         x <- holeName
         pure (PHole (MkFC fname start end) False x)
  <|> do (start, end) <- position
         pragma "MkWorld"
         pure (PPrimVal (MkFC fname start end) WorldVal)
  <|> do (start, end) <- position
         pragma "World"
         pure (PPrimVal (MkFC fname start end) WorldType)
  <|> do (start, end) <- position
         pragma "search"
         pure (PSearch (MkFC fname start end) 50)

whereBlock : FileName -> Int -> Rule (List PDecl)
whereBlock fname col
    = do keyword "where"
         ds <- blockAfter col (topDecl fname)
         pure (collectDefs (concat ds))

-- Expect a keyword, but if we get anything else it's a fatal error
commitKeyword : IndentInfo -> String -> Rule ()
commitKeyword indents req
    = do mustContinue indents (Just req)
         keyword req
         mustContinue indents Nothing

commitSymbol : String -> Rule ()
commitSymbol req
    = symbol req
       <|> fatalError ("Expected '" ++ req ++ "'")

continueWith : IndentInfo -> String -> Rule ()
continueWith indents req
    = do mustContinue indents (Just req)
         symbol req

iOperator : Rule Name
iOperator
    = operator
  <|> do symbol "`"
         n <- name
         symbol "`"
         pure n

data ArgType
    = ExpArg PTerm
    | ImpArg (Maybe Name) PTerm
    | WithArg PTerm

argTerm : ArgType -> PTerm
argTerm (ExpArg t) = t
argTerm (ImpArg _ t) = t
argTerm (WithArg t) = t

mutual
  appExpr : ParseOpts -> FileName -> IndentInfo -> Rule PTerm
  appExpr q fname indents
      = case_ fname indents
    <|> doBlock fname indents
    <|> lambdaCase fname indents
    <|> lazy fname indents
    <|> if_ fname indents
    <|> with_ fname indents
    <|> do start <- location
           f <- simpleExpr fname indents
           args <- many (argExpr q fname indents)
           end <- pure $ endPos $ getPTermLoc $ fromMaybe f $ argTerm <$> last' args
           pure (applyExpImp start end f args)
    <|> do start <- location
           op <- iOperator
           arg <- expr pdef fname indents
           end <- pure $ endPos $ getPTermLoc arg
           pure (PPrefixOp (MkFC fname start end) op arg)
    <|> fail "Expected 'case', 'if', 'do', application or operator expression"
    where
      applyExpImp : FilePos -> FilePos -> PTerm ->
                    List ArgType ->
                    PTerm
      applyExpImp start end f [] = f
      applyExpImp start end f (ExpArg exp :: args)
          = applyExpImp start end (PApp (MkFC fname start end) f exp) args
      applyExpImp start end f (ImpArg n imp :: args)
          = applyExpImp start end (PImplicitApp (MkFC fname start end) f n imp) args
      applyExpImp start end f (WithArg exp :: args)
          = applyExpImp start end (PWithApp (MkFC fname start end) f exp) args

  argExpr : ParseOpts -> FileName -> IndentInfo -> Rule ArgType
  argExpr q fname indents
      = do continue indents
           arg <- simpleExpr fname indents
           the (SourceEmptyRule _) $ case arg of
                PHole loc _ n => pure (ExpArg (PHole loc True n))
                t => pure (ExpArg t)
    <|> do continue indents
           arg <- implicitArg fname indents
           pure (ImpArg (fst arg) (snd arg))
    <|> if withOK q
           then do continue indents
                   symbol "|"
                   arg <- expr (record {withOK = False} q) fname indents
                   pure (WithArg arg)
           else fail "| not allowed here"

  implicitArg : FileName -> IndentInfo -> Rule (Maybe Name, PTerm)
  implicitArg fname indents
      = do start <- location
           symbol "{"
           x <- unqualifiedName
           (do symbol "="
               commit
               tm <- expr pdef fname indents
               symbol "}"
               pure (Just (UN x), tm))
             <|> (do end <- endLocation
                     symbol "}"
                     pure (Just (UN x), PRef (MkFC fname start end) (UN x)))
    <|> do symbol "@{"
           commit
           tm <- expr pdef fname indents
           symbol "}"
           pure (Nothing, tm)

  with_ : FileName -> IndentInfo -> Rule PTerm
  with_ fname indents
      = do start <- location
           keyword "with"
           commit
           ns <- singleName <|> nameList
           end <- location
           rhs <- expr pdef fname indents
           pure (PWithUnambigNames (MkFC fname start end) ns rhs)
    where
      singleName : Rule (List Name)
      singleName = do
        n <- name
        pure [n]

      nameList : Rule (List Name)
      nameList = do
        symbol "["
        commit
        ns <- sepBy1 (symbol ",") name
        symbol "]"
        pure ns

  opExpr : ParseOpts -> FileName -> IndentInfo -> Rule PTerm
  opExpr q fname indents
      = do start <- location
           l <- appExpr q fname indents
           (if eqOK q
               then do continue indents
                       symbol "="
                       r <- opExpr q fname indents
                       end <- pure $ endPos $ getPTermLoc r
                       pure (POp (MkFC fname start end) (UN "=") l r)
               else fail "= not allowed")
             <|>
             (do continue indents
                 op <- iOperator
                 middle <- location
                 r <- opExpr q fname indents
                 end <- pure $ endPos $ getPTermLoc r
                 pure (POp (MkFC fname start end) op l r))
               <|> pure l

  dpair : FileName -> FilePos -> IndentInfo -> Rule PTerm
  dpair fname start indents
      = do x <- unqualifiedName
           symbol ":"
           ty <- expr pdef fname indents
           loc <- pure $ endPos $ getPTermLoc ty
           symbol "**"
           rest <- dpair fname loc indents <|> expr pdef fname indents
           end <- pure $ endPos $ getPTermLoc rest
           pure (PDPair (MkFC fname start end)
                        (PRef (MkFC fname start loc) (UN x))
                        ty
                        rest)
    <|> do l <- expr pdef fname indents
           loc <- location
           symbol "**"
           rest <- dpair fname loc indents <|> expr pdef fname indents
           end <- pure $ endPos $ getPTermLoc rest
           pure (PDPair (MkFC fname start end)
                        l
                        (PImplicit (MkFC fname start end))
                        rest)

  bracketedExpr : FileName -> FilePos -> IndentInfo -> Rule PTerm
  bracketedExpr fname start indents
      -- left section. This may also be a prefix operator, but we'll sort
      -- that out when desugaring: if the operator is infix, treat it as a
      -- section otherwise treat it as prefix
      = do op <- iOperator
           e <- expr pdef fname indents
           continueWith indents ")"
           end <- location
           pure (PSectionL (MkFC fname start end) op e)
    <|> do  -- (.y.z)  -- section of projection (chain)
          start <- location
          projs <- some $ postfixApp fname indents
          args <- many $ simpleExpr fname indents
          end <- location
          symbol ")"
          pure $ PPostfixProjsSection (MkFC fname start end) projs args
      -- unit type/value
    <|> do continueWith indents ")"
           end <- location
           pure (PUnit (MkFC fname start end))
      -- right section (1-tuple is just an expression)
    <|> do p <- dpair fname start indents
           symbol ")"
           pure p
    <|> do e <- expr pdef fname indents
           (do op <- iOperator
               end <- endLocation
               symbol ")"
               pure (PSectionR (MkFC fname start end) e op)
             <|>
            -- all the other bracketed expressions
            tuple fname start indents e)

  getInitRange : List PTerm -> SourceEmptyRule (PTerm, Maybe PTerm)
  getInitRange [x] = pure (x, Nothing)
  getInitRange [x, y] = pure (x, Just y)
  getInitRange _ = fatalError "Invalid list range syntax"

  listRange : FileName -> FilePos -> IndentInfo -> List PTerm -> Rule PTerm
  listRange fname start indents xs
      = do end <- endLocation
           symbol "]"
           let fc = MkFC fname start end
           rstate <- getInitRange xs
           pure (PRangeStream fc (fst rstate) (snd rstate))
    <|> do y <- expr pdef fname indents
           end <- endLocation
           symbol "]"
           let fc = MkFC fname start end
           rstate <- getInitRange xs
           pure (PRange fc (fst rstate) (snd rstate) y)

  listExpr : FileName -> FilePos -> IndentInfo -> Rule PTerm
  listExpr fname start indents
      = do ret <- expr pnowith fname indents
           let endRet = getPTermLoc ret
           symbol "|"
           conds <- sepBy1 (symbol ",") (doAct fname indents)
           end <- pure $ endPos $ fromMaybe endRet (map getLoc $ join $ last' <$> last' conds)
           symbol "]"
           pure (PComprehension (MkFC fname start end) ret (concat conds))
    <|> do xs <- sepBy (symbol ",") (expr pdef fname indents)
           (do symbol ".."
               listRange fname start indents xs)
             <|> (do end <- endLocation
                     symbol "]"
                     pure (PList (MkFC fname start end) xs))

  -- A pair, dependent pair, or just a single expression
  tuple : FileName -> FilePos -> IndentInfo -> PTerm -> Rule PTerm
  tuple fname start indents e
      = do rest <- some (do symbol ","
                            estart <- location
                            el <- expr pdef fname indents
                            pure (estart, el))
           continueWith indents ")"
           end <- location
           pure (PPair (MkFC fname start end) e
                       (mergePairs end rest))
     <|> do continueWith indents ")"
            end <- location
            pure (PBracketed (MkFC fname start end) e)
    where
      mergePairs : FilePos -> List (FilePos, PTerm) -> PTerm
      mergePairs end [] = PUnit (MkFC fname start end)
      mergePairs end [(estart, exp)] = exp
      mergePairs end ((estart, exp) :: rest)
          = PPair (MkFC fname estart end) exp (mergePairs end rest)

  postfixApp : FileName -> IndentInfo -> Rule PTerm
  postfixApp fname indents
    = do
        start <- location
        di <- dotIdent
        end <- location
        pure $ PRef (MkFC fname start end) di
    <|> do
        symbol ".("
        commit
        e <- expr pdef fname indents
        symbol ")"
        pure e

  simpleExpr : FileName -> IndentInfo -> Rule PTerm
  simpleExpr fname indents
    = do  -- x.y.z
          start <- location
          root <- simplerExpr fname indents
          projs <- many $ postfixApp fname indents
          end <- location
          pure $ case projs of
            [] => root
            _  => PPostfixProjs (MkFC fname start end) root projs

  simplerExpr : FileName -> IndentInfo -> Rule PTerm
  simplerExpr fname indents
      = do start <- location
           x <- unqualifiedName
           symbol "@"
           commit
           expr <- simpleExpr fname indents
           end <- pure $ endPos $ getPTermLoc expr
           pure (PAs (MkFC fname start end) (UN x) expr)
    <|> atom fname
    <|> binder fname indents
    <|> rewrite_ fname indents
    <|> record_ fname indents
    <|> do start <- location
           symbol ".("
           commit
           e <- expr pdef fname indents
           end <- endLocation
           symbol ")"
           pure (PDotted (MkFC fname start end) e)
    <|> do start <- location
           symbol "`("
           e <- expr pdef fname indents
           end <- endLocation
           symbol ")"
           pure (PQuote (MkFC fname start end) e)
    <|> do start <- location
           symbol "`{{"
           n <- name
           end <- endLocation
           symbol "}}"
           pure (PQuoteName (MkFC fname start end) n)
    <|> do start <- location
           symbol "`["
           ns <- nonEmptyBlock (topDecl fname)
           end <- endLocation
           symbol "]"
           pure (PQuoteDecl (MkFC fname start end) (collectDefs (concat ns)))
    <|> do start <- location
           symbol "~"
           e <- simpleExpr fname indents
           end <- pure $ endPos $ getPTermLoc e
           pure (PUnquote (MkFC fname start end) e)
    <|> do start <- location
           symbol "("
           bracketedExpr fname start indents
    <|> do start <- location
           symbol "["
           listExpr fname start indents
    <|> do start <- location
           symbol "!"
           e <- simpleExpr fname indents
           end <- pure $ endPos $ getPTermLoc e
           pure (PBang (MkFC fname start end) e)
    <|> do start <- location
           symbol "[|"
           e <- expr pdef fname indents
           end <- pure $ endPos $ getPTermLoc e
           symbol "|]"
           pure (PIdiom (MkFC fname start end) e)
    <|> do start <- location
           pragma "runElab"
           e <- expr pdef fname indents
           end <- pure $ endPos $ getPTermLoc e
           pure (PRunElab (MkFC fname start end) e)
    <|> do start <- location
           pragma "logging"
           lvl <- intLit
           e <- expr pdef fname indents
           end <- pure $ endPos $ getPTermLoc e
           pure (PUnifyLog (MkFC fname start end) (integerToNat lvl) e)

  multiplicity : SourceEmptyRule (Maybe Integer)
  multiplicity
      = do c <- intLit
           pure (Just c)
--     <|> do symbol "&"
--            pure (Just 2) -- Borrowing, not implemented
    <|> pure Nothing

  getMult : Maybe Integer -> SourceEmptyRule RigCount
  getMult (Just 0) = pure erased
  getMult (Just 1) = pure linear
  getMult Nothing = pure top
  getMult _ = fatalError "Invalid multiplicity (must be 0 or 1)"

  pibindAll : FC -> PiInfo PTerm -> List (RigCount, Maybe Name, PTerm) ->
              PTerm -> PTerm
  pibindAll fc p [] scope = scope
  pibindAll fc p ((rig, n, ty) :: rest) scope
           = PPi fc rig p n ty (pibindAll fc p rest scope)

  bindList : FileName -> FilePos -> IndentInfo ->
             Rule (List (RigCount, PTerm, PTerm))
  bindList fname start indents
      = sepBy1 (symbol ",")
               (do rigc <- multiplicity
                   pat <- simpleExpr fname indents
                   ty <- option
                            (PInfer (MkFC fname start start))
                            (do symbol ":"
                                opExpr pdef fname indents)
                   rig <- getMult rigc
                   pure (rig, pat, ty))

  pibindListName : FileName -> FilePos -> IndentInfo ->
                   Rule (List (RigCount, Name, PTerm))
  pibindListName fname start indents
       = do rigc <- multiplicity
            ns <- sepBy1 (symbol ",") binderName
            symbol ":"
            ty <- expr pdef fname indents
            atEnd indents
            rig <- getMult rigc
            pure (map (\n => (rig, UN n, ty)) ns)
     <|> sepBy1 (symbol ",")
                (do rigc <- multiplicity
                    n <- binderName
                    symbol ":"
                    ty <- expr pdef fname indents
                    rig <- getMult rigc
                    pure (rig, UN n, ty))
    where
      -- _ gets treated specially here, it means "I don't care about the name"
      binderName : Rule String
      binderName = unqualifiedName <|> do symbol "_"; pure "_"

  pibindList : FileName -> FilePos -> IndentInfo ->
               Rule (List (RigCount, Maybe Name, PTerm))
  pibindList fname start indents
    = do params <- pibindListName fname start indents
         pure $ map (\(rig, n, ty) => (rig, Just n, ty)) params

  bindSymbol : Rule (PiInfo PTerm)
  bindSymbol
      = do symbol "->"
           pure Explicit
    <|> do symbol "=>"
           pure AutoImplicit


  explicitPi : FileName -> IndentInfo -> Rule PTerm
  explicitPi fname indents
      = do start <- location
           symbol "("
           binders <- pibindList fname start indents
           symbol ")"
           exp <- bindSymbol
           scope <- typeExpr pdef fname indents
           end <- pure $ endPos $ getPTermLoc scope
           pure (pibindAll (MkFC fname start end) exp binders scope)

  autoImplicitPi : FileName -> IndentInfo -> Rule PTerm
  autoImplicitPi fname indents
      = do start <- location
           symbol "{"
           keyword "auto"
           commit
           binders <- pibindList fname start indents
           symbol "}"
           symbol "->"
           scope <- typeExpr pdef fname indents
           end <- pure $ endPos $ getPTermLoc scope
           pure (pibindAll (MkFC fname start end) AutoImplicit binders scope)

  defaultImplicitPi : FileName -> IndentInfo -> Rule PTerm
  defaultImplicitPi fname indents
      = do start <- location
           symbol "{"
           keyword "default"
           commit
           t <- simpleExpr fname indents
           binders <- pibindList fname start indents
           symbol "}"
           symbol "->"
           scope <- typeExpr pdef fname indents
           end <- pure $ endPos $ getPTermLoc scope
           pure (pibindAll (MkFC fname start end) (DefImplicit t) binders scope)

  forall_ : FileName -> IndentInfo -> Rule PTerm
  forall_ fname indents
      = do start <- location
           keyword "forall"
           commit
           nstart <- location
           ns <- sepBy1 (symbol ",") unqualifiedName
           nend <- location
           let nfc = MkFC fname nstart nend
           let binders = map (\n => (erased {a=RigCount},
                                     Just (UN n), PImplicit nfc)) ns
           symbol "."
           scope <- typeExpr pdef fname indents
           end <- pure $ endPos $ getPTermLoc scope
           pure (pibindAll (MkFC fname start end) Implicit binders scope)

  implicitPi : FileName -> IndentInfo -> Rule PTerm
  implicitPi fname indents
      = do start <- location
           symbol "{"
           binders <- pibindList fname start indents
           symbol "}"
           symbol "->"
           scope <- typeExpr pdef fname indents
           end <- pure $ endPos $ getPTermLoc scope
           pure (pibindAll (MkFC fname start end) Implicit binders scope)

  lam : FileName -> IndentInfo -> Rule PTerm
  lam fname indents
      = do start <- location
           symbol "\\"
           binders <- bindList fname start indents
           symbol "=>"
           mustContinue indents Nothing
           scope <- expr pdef fname indents
           end <- pure $ endPos $ getPTermLoc scope
           pure (bindAll (MkFC fname start end) binders scope)
     where
       bindAll : FC -> List (RigCount, PTerm, PTerm) -> PTerm -> PTerm
       bindAll fc [] scope = scope
       bindAll fc ((rig, pat, ty) :: rest) scope
           = PLam fc rig Explicit pat ty (bindAll fc rest scope)

  letBinder : FileName -> IndentInfo ->
              Rule (FilePos, FilePos, RigCount, PTerm, PTerm, PTerm, List PClause)
  letBinder fname indents
      = do start <- location
           rigc <- multiplicity
           pat <- expr plhs fname indents
           tyend <- pure $ endPos $ getPTermLoc pat
           ty <- option (PImplicit (MkFC fname start tyend))
                        (do symbol ":"
                            typeExpr (pnoeq pdef) fname indents)
           symbol "="
           val <- expr pnowith fname indents
           alts <- block (patAlt fname)
           end <- location
           end <- pure $ fromMaybe end (endPos <$> getPClauseLoc <$> last' alts)
           rig <- getMult rigc
           pure (start, end, rig, pat, ty, val, alts)

  buildLets : FileName ->
              List (FilePos, FilePos, RigCount, PTerm, PTerm, PTerm, List PClause) ->
              PTerm -> PTerm
  buildLets fname [] sc = sc
  buildLets fname ((start, end, rig, pat, ty, val, alts) :: rest) sc
      = let fc = MkFC fname start end in
            PLet fc rig pat ty val
                 (buildLets fname rest sc) alts

  buildDoLets : FileName ->
                List (FilePos, FilePos, RigCount, PTerm, PTerm, PTerm, List PClause) ->
                List PDo
  buildDoLets fname [] = []
  buildDoLets fname ((start, end, rig, PRef fc' (UN n), ty, val, []) :: rest)
      = let fc = MkFC fname start end in
            if lowerFirst n
               then DoLet fc (UN n) rig ty val :: buildDoLets fname rest
               else DoLetPat fc (PRef fc' (UN n)) ty val []
                         :: buildDoLets fname rest
  buildDoLets fname ((start, end, rig, pat, ty, val, alts) :: rest)
      = let fc = MkFC fname start end in
            DoLetPat fc pat ty val alts :: buildDoLets fname rest

  let_ : FileName -> IndentInfo -> Rule PTerm
  let_ fname indents
      = do start <- location
           keyword "let"
           res <- nonEmptyBlock (letBinder fname)
           commitKeyword indents "in"
           scope <- typeExpr pdef fname indents
           end <- pure $ endPos $ getPTermLoc scope
           pure (buildLets fname res scope)

    <|> do start <- location
           keyword "let"
           commit
           ds <- nonEmptyBlock (topDecl fname)
           commitKeyword indents "in"
           scope <- typeExpr pdef fname indents
           end <- pure $ endPos $ getPTermLoc scope
           pure (PLocal (MkFC fname start end) (collectDefs (concat ds)) scope)

  case_ : FileName -> IndentInfo -> Rule PTerm
  case_ fname indents
      = do start <- location
           keyword "case"
           scr <- expr pdef fname indents
           commitKeyword indents "of"
           alts <- block (caseAlt fname)
           end <- location
           end <- pure $ fromMaybe end (endPos <$> getPClauseLoc <$> last' alts)
           pure (PCase (MkFC fname start end) scr alts)

  lambdaCase : FileName -> IndentInfo -> Rule PTerm
  lambdaCase fname indents
      = do start <- location
           symbol "\\"
           endCase <- endLocation
           keyword "case"
           commit
           alts <- block (caseAlt fname)
           end <- location
           end <- pure $ fromMaybe end (endPos <$> getPClauseLoc <$> last' alts)
           pure $
            (let fc = MkFC fname start end
                 fcCase = MkFC fname start endCase
                 n = MN "lcase" 0 in
              PLam fcCase top Explicit (PRef fcCase n) (PInfer fcCase) $
                PCase fc (PRef fcCase n) alts)

  caseAlt : FileName -> IndentInfo -> Rule PClause
  caseAlt fname indents
      = do start <- location
           lhs <- opExpr plhs fname indents
           caseRHS fname start indents lhs

  caseRHS : FileName -> FilePos -> IndentInfo -> PTerm -> Rule PClause
  caseRHS fname start indents lhs
      = do symbol "=>"
           mustContinue indents Nothing
           rhs <- expr pdef fname indents
           end <- pure $ endPos $ getPTermLoc rhs
           atEnd indents
           pure (MkPatClause (MkFC fname start end) lhs rhs [])
    <|> do end <- endLocation
           keyword "impossible"
           atEnd indents
           pure (MkImpossible (MkFC fname start end) lhs)

  if_ : FileName -> IndentInfo -> Rule PTerm
  if_ fname indents
      = do start <- location
           keyword "if"
           x <- expr pdef fname indents
           commitKeyword indents "then"
           t <- expr pdef fname indents
           commitKeyword indents "else"
           e <- expr pdef fname indents
           atEnd indents
           end <- location
           pure (PIfThenElse (MkFC fname start end) x t e)

  record_ : FileName -> IndentInfo -> Rule PTerm
  record_ fname indents
      = do start <- location
           keyword "record"
           symbol "{"
           commit
           fs <- sepBy1 (symbol ",") (field fname indents)
           end <- endLocation
           symbol "}"
           pure (PUpdate (MkFC fname start end) fs)

  field : FileName -> IndentInfo -> Rule PFieldUpdate
  field fname indents
      = do path <- map fieldName <$> [| name :: many recFieldCompat |]
           upd <- (do symbol "="; pure PSetField)
                      <|>
                  (do symbol "$="; pure PSetFieldApp)
           val <- opExpr plhs fname indents
           pure (upd path val)
    where
      fieldName : Name -> String
      fieldName (UN s) = s
      fieldName _ = "_impossible"

      -- this allows the dotted syntax .field
      -- but also the arrowed syntax ->field for compatibility with Idris 1
      recFieldCompat : Rule Name
      recFieldCompat = dotIdent <|> (symbol "->" *> name)

  rewrite_ : FileName -> IndentInfo -> Rule PTerm
  rewrite_ fname indents
      = do start <- location
           keyword "rewrite"
           rule <- expr pdef fname indents
           commitKeyword indents "in"
           tm <- expr pdef fname indents
           end <- pure $ endPos $ getPTermLoc tm
           pure (PRewrite (MkFC fname start end) rule tm)

  doBlock : FileName -> IndentInfo -> Rule PTerm
  doBlock fname indents
      = do start <- location
           keyword "do"
           actions <- block (doAct fname)
           end <- location
           end <- pure $ fromMaybe end $ map (endPos . getLoc) $ join $ last' <$> last' actions
           pure (PDoBlock (MkFC fname start end) Nothing (concat actions))
    <|> do start <- location
           nsdo <- namespacedIdent
           the (SourceEmptyRule PTerm) $ case nsdo of
                ("do" :: ns) =>
                   do actions <- block (doAct fname)
                      end <- location
                      end <- pure $ fromMaybe end $ map (endPos . getLoc) $ join $ last' <$> last' actions
                      pure (PDoBlock (MkFC fname start end)
                                     (Just (reverse ns)) (concat actions))
                _ => fail "Not a namespaced 'do'"

  lowerFirst : String -> Bool
  lowerFirst "" = False
  lowerFirst str = assert_total (isLower (prim__strHead str))

  validPatternVar : Name -> SourceEmptyRule ()
  validPatternVar (UN n)
      = if lowerFirst n then pure ()
                        else fail "Not a pattern variable"
  validPatternVar _ = fail "Not a pattern variable"

  doAct : FileName -> IndentInfo -> Rule (List PDo)
  doAct fname indents
      = do start <- location
           n <- name
           -- If the name doesn't begin with a lower case letter, we should
           -- treat this as a pattern, so fail
           validPatternVar n
           symbol "<-"
           val <- expr pdef fname indents
           end <- pure $ endPos $ getPTermLoc val
           atEnd indents
           pure [DoBind (MkFC fname start end) n val]
    <|> do keyword "let"
           res <- block (letBinder fname)
           atEnd indents
           pure (buildDoLets fname res)
    <|> do start <- location
           keyword "let"
           res <- block (topDecl fname)
           end <- location
           end <- pure $ fromMaybe end $ map (endPos . getPDeclLoc) $ join $ last' <$> last' res
           atEnd indents
           pure [DoLetLocal (MkFC fname start end) (concat res)]
    <|> do start <- location
           keyword "rewrite"
           rule <- expr pdef fname indents
           end <- pure $ endPos $ getPTermLoc rule
           atEnd indents
           pure [DoRewrite (MkFC fname start end) rule]
    <|> do start <- location
           e <- expr plhs fname indents
           (do atEnd indents
               end <- pure $ endPos $ getPTermLoc e
               pure [DoExp (MkFC fname start end) e])
             <|> (do symbol "<-"
                     val <- expr pnowith fname indents
                     alts <- block (patAlt fname)
                     end <- location
                     end <- pure $ fromMaybe end $ (endPos . getPClauseLoc) <$> last' alts
                     atEnd indents
                     pure [DoBindPat (MkFC fname start end) e val alts])

  patAlt : FileName -> IndentInfo -> Rule PClause
  patAlt fname indents
      = do symbol "|"
           caseAlt fname indents

  lazy : FileName -> IndentInfo -> Rule PTerm
  lazy fname indents
      = do start <- location
           exactIdent "Lazy"
           tm <- simpleExpr fname indents
           end <- pure $ endPos $ getPTermLoc tm
           pure (PDelayed (MkFC fname start end) LLazy tm)
    <|> do start <- location
           exactIdent "Inf"
           tm <- simpleExpr fname indents
           end <- pure $ endPos $ getPTermLoc tm
           pure (PDelayed (MkFC fname start end) LInf tm)
    <|> do start <- location
           exactIdent "Delay"
           tm <- simpleExpr fname indents
           end <- pure $ endPos $ getPTermLoc tm
           pure (PDelay (MkFC fname start end) tm)
    <|> do start <- location
           exactIdent "Force"
           tm <- simpleExpr fname indents
           end <- pure $ endPos $ getPTermLoc tm
           pure (PForce (MkFC fname start end) tm)

  binder : FileName -> IndentInfo -> Rule PTerm
  binder fname indents
      = let_ fname indents
    <|> autoImplicitPi fname indents
    <|> defaultImplicitPi fname indents
    <|> forall_ fname indents
    <|> implicitPi fname indents
    <|> explicitPi fname indents
    <|> lam fname indents

  typeExpr : ParseOpts -> FileName -> IndentInfo -> Rule PTerm
  typeExpr q fname indents
      = do start <- location
           arg <- opExpr q fname indents
           (do continue indents
               rest <- some (do exp <- bindSymbol
                                op <- opExpr pdef fname indents
                                pure (exp, op))
               end <- location
               end <- pure $ fromMaybe end $ (endPos . getPTermLoc . snd) <$> last' rest
               pure (mkPi start end arg rest))
             <|> pure arg
    where
      mkPi : FilePos -> FilePos -> PTerm -> List (PiInfo PTerm, PTerm) -> PTerm
      mkPi start end arg [] = arg
      mkPi start end arg ((exp, a) :: as)
            = PPi (MkFC fname start end) top exp Nothing arg
                  (mkPi start end a as)

  export
  expr : ParseOpts -> FileName -> IndentInfo -> Rule PTerm
  expr = typeExpr

visOption : Rule Visibility
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

tyDecl : String -> FileName -> IndentInfo -> Rule PTypeDecl
tyDecl predoc fname indents
    = do start <- location
         doc   <- option "" documentation
         n     <- name
         symbol ":"
         mustWork $
            do ty  <- expr pdef fname indents
               end <- pure $ endPos $ getPTermLoc ty
               atEnd indents
               pure (MkPTy (MkFC fname start end) n (predoc ++ doc) ty)

withFlags : SourceEmptyRule (List WithFlag)
withFlags
    = do pragma "syntactic"
         fs <- withFlags
         pure $ Syntactic :: fs
  <|> pure []

mutual
  parseRHS : (withArgs : Nat) ->
             FileName -> FilePos -> Int ->
             IndentInfo -> (lhs : PTerm) -> Rule PClause
  parseRHS withArgs fname start col indents lhs
       = do symbol "="
            mustWork $
              do rhs <- expr pdef fname indents
                 ws <- option [] (whereBlock fname col)
                 atEnd indents
                 end <- location
                 pure (MkPatClause (MkFC fname start end) lhs rhs ws)
     <|> do keyword "with"
            wstart <- location
            flags <- withFlags
            symbol "("
            wval <- bracketedExpr fname wstart indents
            ws <- nonEmptyBlock (clause (S withArgs) fname)
            end <- location
            pure (MkWithClause (MkFC fname start end) lhs wval flags ws)
     <|> do end <- endLocation
            keyword "impossible"
            atEnd indents
            pure (MkImpossible (MkFC fname start end) lhs)

  ifThenElse : Bool -> Lazy t -> Lazy t -> t
  ifThenElse True t e = t
  ifThenElse False t e = e

  clause : Nat -> FileName -> IndentInfo -> Rule PClause
  clause withArgs fname indents
      = do start <- location
           col <- column
           lhs <- expr plhs fname indents
           extra <- many parseWithArg
           -- Can't have the dependent 'if' here since we won't be able
           -- to infer the termination status of the rule
           ifThenElse (withArgs /= length extra)
              (fatalError "Wrong number of 'with' arguments")
              (parseRHS withArgs fname start col indents (applyArgs lhs extra))
    where
      applyArgs : PTerm -> List (FC, PTerm) -> PTerm
      applyArgs f [] = f
      applyArgs f ((fc, a) :: args) = applyArgs (PApp fc f a) args

      parseWithArg : Rule (FC, PTerm)
      parseWithArg
          = do symbol "|"
               start <- location
               tm <- expr plhs fname indents
               end <- pure $ endPos $ getPTermLoc tm
               pure (MkFC fname start end, tm)

mkTyConType : FC -> List Name -> PTerm
mkTyConType fc [] = PType fc
mkTyConType fc (x :: xs)
   = PPi fc linear Explicit Nothing (PType fc) (mkTyConType fc xs)

mkDataConType : FC -> PTerm -> List ArgType -> PTerm
mkDataConType fc ret [] = ret
mkDataConType fc ret (ExpArg x :: xs)
    = PPi fc linear Explicit Nothing x (mkDataConType fc ret xs)
mkDataConType fc ret (ImpArg n (PRef fc' x) :: xs)
    = if n == Just x
         then PPi fc linear Implicit n (PType fc')
                          (mkDataConType fc ret xs)
         else PPi fc linear Implicit n (PRef fc' x)
                          (mkDataConType fc ret xs)
mkDataConType fc ret (ImpArg n x :: xs)
    = PPi fc linear Implicit n x (mkDataConType fc ret xs)
mkDataConType fc ret (WithArg a :: xs)
    = PImplicit fc -- This can't happen because we parse constructors without
                   -- withOK set

simpleCon : FileName -> PTerm -> IndentInfo -> Rule PTypeDecl
simpleCon fname ret indents
    = do start <- location
         cdoc   <- option "" documentation
         cname  <- name
         params <- many (argExpr plhs fname indents)
         end <- location
         end <- pure $ fromMaybe end $ (endPos . getPTermLoc . argTerm) <$> last' params
         atEnd indents
         pure (let cfc = MkFC fname start end in
                   MkPTy cfc cname cdoc (mkDataConType cfc ret params))

simpleData : FileName -> FilePos -> Name -> IndentInfo -> Rule PDataDecl
simpleData fname start n indents
    = do params <- many name
         tyend <- location
         let tyfc = MkFC fname start tyend
         symbol "="
         let conRetTy = papply tyfc (PRef tyfc n)
                           (map (PRef tyfc) params)
         cons <- sepBy1 (symbol "|")
                        (simpleCon fname conRetTy indents)
         end <- location
         end <- pure $ fromMaybe end $ (endPos . getPTypeDeclLoc) <$> last' cons
         pure (MkPData (MkFC fname start end) n
                       (mkTyConType tyfc params) [] cons)

dataOpt : Rule DataOpt
dataOpt
    = do exactIdent "noHints"
         pure NoHints
  <|> do exactIdent "uniqueSearch"
         pure UniqueSearch
  <|> do exactIdent "search"
         ns <- some name
         pure (SearchBy ns)
  <|> do exactIdent "external"
         pure External
  <|> do exactIdent "noNewtype"
         pure NoNewtype

dataBody : FileName -> Int -> FilePos -> Name -> IndentInfo -> PTerm ->
          SourceEmptyRule PDataDecl
dataBody fname mincol start n indents ty
    = do atEndIndent indents
         end <- location
         pure (MkPLater (MkFC fname start end) n ty)
  <|> do keyword "where"
         opts <- option [] (do symbol "["
                               dopts <- sepBy1 (symbol ",") dataOpt
                               symbol "]"
                               pure dopts)
         cs <- blockAfter mincol (tyDecl "" fname)
         end <- location
         end <- pure $ fromMaybe end $ (endPos . getPTypeDeclLoc) <$> last' cs
         pure (MkPData (MkFC fname start end) n ty opts cs)

gadtData : FileName -> Int -> FilePos -> Name -> IndentInfo -> Rule PDataDecl
gadtData fname mincol start n indents
    = do symbol ":"
         commit
         ty <- expr pdef fname indents
         dataBody fname mincol start n indents ty

dataDeclBody : FileName -> IndentInfo -> Rule PDataDecl
dataDeclBody fname indents
    = do start <- location
         col <- column
         keyword "data"
         n <- name
         simpleData fname start n indents
           <|> gadtData fname col start n indents

dataDecl : FileName -> IndentInfo -> Rule PDecl
dataDecl fname indents
    = do start <- location
         doc   <- option "" documentation
         vis   <- visibility
         dat   <- dataDeclBody fname indents
         end   <- location
         end   <- pure $ endPos $ getPDataDeclLoc dat
         pure (PData (MkFC fname start end) doc vis dat)

stripBraces : String -> String
stripBraces str = pack (drop '{' (reverse (drop '}' (reverse (unpack str)))))
  where
    drop : Char -> List Char -> List Char
    drop c [] = []
    drop c (c' :: xs) = if c == c' then drop c xs else c' :: xs

onoff : Rule Bool
onoff
   = do exactIdent "on"
        pure True
 <|> do exactIdent "off"
        pure False

extension : Rule LangExt
extension
    = do exactIdent "ElabReflection"
         pure ElabReflection
  <|> do exactIdent "PostfixProjections"
         pure PostfixProjections
  <|> do exactIdent "Borrowing"
         pure Borrowing

totalityOpt : Rule TotalReq
totalityOpt
    = do keyword "partial"
         pure PartialOK
  <|> do keyword "total"
         pure Total
  <|> do keyword "covering"
         pure CoveringOnly

directive : FileName -> IndentInfo -> Rule Directive
directive fname indents
    = do pragma "hide"
         n <- name
         atEnd indents
         pure (Hide n)
--   <|> do pragma "hide_export"
--          n <- name
--          atEnd indents
--          pure (Hide True n)
  <|> do pragma "logging"
         lvl <- intLit
         atEnd indents
         pure (Logging (fromInteger lvl))
  <|> do pragma "auto_lazy"
         b <- onoff
         atEnd indents
         pure (LazyOn b)
  <|> do pragma "unbound_implicits"
         b <- onoff
         atEnd indents
         pure (UnboundImplicits b)
  <|> do pragma "ambiguity_depth"
         lvl <- intLit
         atEnd indents
         pure (AmbigDepth (fromInteger lvl))
  <|> do pragma "auto_implicit_depth"
         dpt <- intLit
         atEnd indents
         pure (AutoImplicitDepth (fromInteger dpt))
  <|> do pragma "pair"
         ty <- name
         f <- name
         s <- name
         atEnd indents
         pure (PairNames ty f s)
  <|> do pragma "rewrite"
         eq <- name
         rw <- name
         atEnd indents
         pure (RewriteName eq rw)
  <|> do pragma "integerLit"
         n <- name
         atEnd indents
         pure (PrimInteger n)
  <|> do pragma "stringLit"
         n <- name
         atEnd indents
         pure (PrimString n)
  <|> do pragma "charLit"
         n <- name
         atEnd indents
         pure (PrimChar n)
  <|> do pragma "name"
         n <- name
         ns <- sepBy1 (symbol ",") unqualifiedName
         atEnd indents
         pure (Names n ns)
  <|> do pragma "start"
         e <- expr pdef fname indents
         atEnd indents
         pure (StartExpr e)
  <|> do pragma "allow_overloads"
         n <- name
         atEnd indents
         pure (Overloadable n)
  <|> do pragma "language"
         e <- extension
         atEnd indents
         pure (Extension e)
  <|> do pragma "default"
         tot <- totalityOpt
         atEnd indents
         pure (DefaultTotality tot)

fix : Rule Fixity
fix
    = do keyword "infixl"; pure InfixL
  <|> do keyword "infixr"; pure InfixR
  <|> do keyword "infix"; pure Infix
  <|> do keyword "prefix"; pure Prefix

namespaceHead : Rule (List String)
namespaceHead
    = do keyword "namespace"
         commit
         ns <- namespacedIdent
         pure ns

namespaceDecl : FileName -> IndentInfo -> Rule PDecl
namespaceDecl fname indents
    = do start <- location
         doc   <- option "" documentation
         col   <- column
         ns    <- namespaceHead
         end   <- location
         ds    <- blockAfter col (topDecl fname)
         pure (PNamespace (MkFC fname start end) ns (concat ds))

transformDecl : FileName -> IndentInfo -> Rule PDecl
transformDecl fname indents
    = do start <- location
         pragma "transform"
         n <- strLit
         lhs <- expr plhs fname indents
         symbol "="
         rhs <- expr pnowith fname indents
         end <- pure $ endPos $ getPTermLoc rhs
         pure (PTransform (MkFC fname start end) n lhs rhs)

runElabDecl : FileName -> IndentInfo -> Rule PDecl
runElabDecl fname indents
    = do start <- location
         pragma "runElab"
         tm <- expr pnowith fname indents
         end <- pure $ endPos $ getPTermLoc tm
         pure (PRunElabDecl (MkFC fname start end) tm)

mutualDecls : FileName -> IndentInfo -> Rule PDecl
mutualDecls fname indents
    = do start <- location
         keyword "mutual"
         commit
         ds <- assert_total (nonEmptyBlock (topDecl fname))
         end <- location
         end <- pure $ fromMaybe end $ map (endPos . getPDeclLoc) $ join $ last' <$> last' ds
         pure (PMutual (MkFC fname start end) (concat ds))

paramDecls : FileName -> IndentInfo -> Rule PDecl
paramDecls fname indents
    = do start <- location
         keyword "parameters"
         commit
         symbol "("
         ps <- sepBy (symbol ",")
                     (do x <- unqualifiedName
                         symbol ":"
                         ty <- typeExpr pdef fname indents
                         pure (UN x, ty))
         symbol ")"
         ds <- assert_total (nonEmptyBlock (topDecl fname))
         end <- location
         end <- pure $ fromMaybe end $ map (endPos . getPDeclLoc) $ join $ last' <$> last' ds
         pure (PParameters (MkFC fname start end) ps (collectDefs (concat ds)))

usingDecls : FileName -> IndentInfo -> Rule PDecl
usingDecls fname indents
    = do start <- location
         keyword "using"
         commit
         symbol "("
         us <- sepBy (symbol ",")
                     (do n <- option Nothing
                                (do x <- unqualifiedName
                                    symbol ":"
                                    pure (Just (UN x)))
                         ty <- typeExpr pdef fname indents
                         pure (n, ty))
         symbol ")"
         ds <- assert_total (nonEmptyBlock (topDecl fname))
         end <- location
         end <- pure $ fromMaybe end $ map (endPos . getPDeclLoc) $ join $ last' <$> last' ds
         pure (PUsing (MkFC fname start end) us (collectDefs (concat ds)))

fnOpt : Rule PFnOpt
fnOpt = do x <- totalityOpt
           pure $ IFnOpt (Totality x)

fnDirectOpt : FileName -> Rule PFnOpt
fnDirectOpt fname
    = do pragma "hint"
         pure $ IFnOpt (Hint True)
  <|> do pragma "globalhint"
         pure $ IFnOpt (GlobalHint False)
  <|> do pragma "defaulthint"
         pure $ IFnOpt (GlobalHint True)
  <|> do pragma "inline"
         commit
         pure $ IFnOpt Inline
  <|> do pragma "tcinline"
         commit
         pure $ IFnOpt TCInline
  <|> do pragma "extern"
         pure $ IFnOpt ExternFn
  <|> do pragma "macro"
         pure $ IFnOpt Macro
  <|> do pragma "spec"
         ns <- sepBy (symbol ",") name
         pure $ IFnOpt (SpecArgs ns)
  <|> do pragma "foreign"
         cs <- block (expr pdef fname)
         pure $ PForeign cs

visOpt : FileName -> Rule (Either Visibility PFnOpt)
visOpt fname
    = do vis <- visOption
         pure (Left vis)
  <|> do tot <- fnOpt
         pure (Right tot)
  <|> do opt <- fnDirectOpt fname
         pure (Right opt)

getVisibility : Maybe Visibility -> List (Either Visibility PFnOpt) ->
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

constraints : FileName -> IndentInfo -> SourceEmptyRule (List (Maybe Name, PTerm))
constraints fname indents
    = do tm <- appExpr pdef fname indents
         symbol "=>"
         more <- constraints fname indents
         pure ((Nothing, tm) :: more)
  <|> do symbol "("
         n <- name
         symbol ":"
         tm <- expr pdef fname indents
         symbol ")"
         symbol "=>"
         more <- constraints fname indents
         pure ((Just n, tm) :: more)
  <|> pure []

implBinds : FileName -> IndentInfo -> SourceEmptyRule (List (Name, RigCount, PTerm))
implBinds fname indents
    = do symbol "{"
         m <- multiplicity
         rig <- getMult m
         n <- name
         symbol ":"
         tm <- expr pdef fname indents
         symbol "}"
         symbol "->"
         more <- implBinds fname indents
         pure ((n, rig, tm) :: more)
  <|> pure []

ifaceParam : FileName -> IndentInfo -> Rule (Name, PTerm)
ifaceParam fname indents
    = do symbol "("
         n <- name
         symbol ":"
         tm <- expr pdef fname indents
         symbol ")"
         pure (n, tm)
  <|> do start <- location
         n <- name
         end <- location
         pure (n, PInfer (MkFC fname start end))

ifaceDecl : FileName -> IndentInfo -> Rule PDecl
ifaceDecl fname indents
    = do start <- location
         doc   <- option "" documentation
         vis   <- visibility
         col   <- column
         keyword "interface"
         commit
         cons   <- constraints fname indents
         n      <- name
         params <- many (ifaceParam fname indents)
         det    <- option []
                     (do symbol "|"
                         sepBy (symbol ",") name)
         keyword "where"
         dc <- option Nothing
                 (do exactIdent "constructor"
                     n <- name
                     pure (Just n))
         body <- assert_total (blockAfter col (topDecl fname))
         end  <- location
         end <- pure $ fromMaybe end $ map (endPos . getPDeclLoc) $ join $ last' <$> last' body
         pure (PInterface (MkFC fname start end)
                      vis cons n doc params det dc (collectDefs (concat body)))

implDecl : FileName -> IndentInfo -> Rule PDecl
implDecl fname indents
    = do start <- location
         doc     <- option "" documentation
         visOpts <- many (visOpt fname)
         vis     <- getVisibility Nothing visOpts
         let opts = mapMaybe getRight visOpts
         col <- column
         option () (keyword "implementation")
         iname <- option Nothing (do symbol "["
                                     iname <- name
                                     symbol "]"
                                     pure (Just iname))
         impls  <- implBinds fname indents
         cons   <- constraints fname indents
         n      <- name
         params <- many (simpleExpr fname indents)
         nusing <- option [] (do keyword "using"
                                 names <- some name
                                 pure names)
         body <- optional (do keyword "where"
                              blockAfter col (topDecl fname))
         atEnd indents
         end <- location
         pure (PImplementation (MkFC fname start end)
                         vis opts Single impls cons n params iname nusing
                         (map (collectDefs . concat) body))

fieldDecl : FileName -> IndentInfo -> Rule (List PField)
fieldDecl fname indents
      = do doc <- option "" documentation
           symbol "{"
           commit
           fs <- fieldBody doc Implicit
           symbol "}"
           atEnd indents
           pure fs
    <|> do doc <- option "" documentation
           fs <- fieldBody doc Explicit
           atEnd indents
           pure fs
  where
    fieldBody : String -> PiInfo PTerm -> Rule (List PField)
    fieldBody doc p
        = do start <- location
             m <- multiplicity
             rigin <- getMult m
             let rig = if isErased rigin then erased else linear
             ns <- sepBy1 (symbol ",") name
             symbol ":"
             ty <- expr pdef fname indents
             end <- pure $ endPos $ getPTermLoc ty
             pure (map (\n => MkField (MkFC fname start end)
                                      doc rig p n ty) ns)

recordParam : FileName -> IndentInfo -> Rule (List (Name, RigCount, PiInfo PTerm,  PTerm))
recordParam fname indents
    = do symbol "("
         start <- location
         params <- pibindListName fname start indents
         symbol ")"
         pure $ map (\(c, n, tm) => (n, c, Explicit, tm)) params
  <|> do symbol "{"
         commit
         info <- the (SourceEmptyRule (PiInfo PTerm))
                 (pure  AutoImplicit <* keyword "auto"
              <|>(do
                  keyword "default"
                  t <- simpleExpr fname indents
                  pure $ DefImplicit t)
              <|> pure      Implicit)
         start <- location
         params <- pibindListName fname start indents
         symbol "}"
         pure $ map (\(c, n, tm) => (n, c, info, tm)) params
  <|> do start <- location
         n <- name
         end <- location
         pure [(n, top, Explicit, PInfer (MkFC fname start end))]

recordDecl : FileName -> IndentInfo -> Rule PDecl
recordDecl fname indents
    = do start <- location
         doc   <- option "" documentation
         vis   <- visibility
         col   <- column
         keyword "record"
         n       <- name
         paramss <- many (recordParam fname indents)
         let params = concat paramss
         keyword "where"
         dcflds <- blockWithOptHeaderAfter col ctor (fieldDecl fname)
         end    <- location
         pure (PRecord (MkFC fname start end)
                       doc vis n params (fst dcflds) (concat (snd dcflds)))
  where
  ctor : IndentInfo -> Rule Name
  ctor idt = do exactIdent "constructor"
                n <- name
                atEnd idt
                pure n

claim : FileName -> IndentInfo -> Rule PDecl
claim fname indents
    = do start   <- location
         doc     <- option "" documentation
         visOpts <- many (visOpt fname)
         vis     <- getVisibility Nothing visOpts
         let opts = mapMaybe getRight visOpts
         m   <- multiplicity
         rig <- getMult m
         cl  <- tyDecl doc fname indents
         end <- pure $ endPos $ getPTypeDeclLoc cl
         pure (PClaim (MkFC fname start end) rig vis opts cl)

definition : FileName -> IndentInfo -> Rule PDecl
definition fname indents
    = do start <- location
         nd    <- clause 0 fname indents
         end   <- pure $ endPos $ getPClauseLoc nd
         pure (PDef (MkFC fname start end) [nd])

fixDecl : FileName -> IndentInfo -> Rule (List PDecl)
fixDecl fname indents
    = do start <- location
         fixity <- fix
         commit
         prec <- intLit
         ops <- sepBy1 (symbol ",") iOperator
         end <- location
         pure (map (PFixity (MkFC fname start end) fixity (fromInteger prec)) ops)

directiveDecl : FileName -> IndentInfo -> Rule PDecl
directiveDecl fname indents
    = do start <- location
         (do d <- directive fname indents
             end <- location
             pure (PDirective (MkFC fname start end) d))
           <|>
          (do pragma "runElab"
              tm <- expr pdef fname indents
              end <- pure $ endPos $ getPTermLoc tm
              atEnd indents
              pure (PReflect (MkFC fname start end) tm))

-- Declared at the top
-- topDecl : FileName -> IndentInfo -> Rule (List PDecl)
topDecl fname indents
    = do d <- dataDecl fname indents
         pure [d]
  <|> do d <- claim fname indents
         pure [d]
  <|> do d <- definition fname indents
         pure [d]
  <|> fixDecl fname indents
  <|> do d <- ifaceDecl fname indents
         pure [d]
  <|> do d <- implDecl fname indents
         pure [d]
  <|> do d <- recordDecl fname indents
         pure [d]
  <|> do d <- namespaceDecl fname indents
         pure [d]
  <|> do d <- mutualDecls fname indents
         pure [d]
  <|> do d <- paramDecls fname indents
         pure [d]
  <|> do d <- usingDecls fname indents
         pure [d]
  <|> do d <- runElabDecl fname indents
         pure [d]
  <|> do d <- transformDecl fname indents
         pure [d]
  <|> do d <- directiveDecl fname indents
         pure [d]
  <|> do start <- location
         dstr <- terminal "Expected CG directive"
                          (\x => case tok x of
                                      CGDirective d => Just d
                                      _ => Nothing)
         end <- location
         pure [let cgrest = span isAlphaNum dstr in
                   PDirective (MkFC fname start end)
                        (CGAction (fst cgrest) (stripBraces (trim (snd cgrest))))]
  <|> fatalError "Couldn't parse declaration"

-- All the clauses get parsed as one-clause definitions. Collect any
-- neighbouring clauses into one definition. This might mean merging two
-- functions which are different, if there are forward declarations,
-- but we'll split them in Desugar.idr. We can't do this now, because we
-- haven't resolved operator precedences yet.
-- Declared at the top.
-- collectDefs : List PDecl -> List PDecl
collectDefs [] = []
collectDefs (PDef annot cs :: ds)
    = let (cs', rest) = spanMap isClause ds in
          PDef annot (cs ++ cs') :: assert_total (collectDefs rest)
  where
    spanMap : (a -> Maybe (List b)) -> List a -> (List b, List a)
    spanMap f [] = ([], [])
    spanMap f (x :: xs) = case f x of
                               Nothing => ([], x :: xs)
                               Just y => case spanMap f xs of
                                              (ys, zs) => (y ++ ys, zs)

    isClause : PDecl -> Maybe (List PClause)
    isClause (PDef annot cs)
        = Just cs
    isClause _ = Nothing
collectDefs (PNamespace annot ns nds :: ds)
    = PNamespace annot ns (collectDefs nds) :: collectDefs ds
collectDefs (PMutual annot nds :: ds)
    = PMutual annot (collectDefs nds) :: collectDefs ds
collectDefs (d :: ds)
    = d :: collectDefs ds

export
import_ : FileName -> IndentInfo -> Rule Import
import_ fname indents
    = do start <- location
         keyword "import"
         reexp <- option False (do keyword "public"
                                   pure True)
         ns <- namespacedIdent
         nsAs <- option ns (do exactIdent "as"
                               namespacedIdent)
         end <- location
         atEnd indents
         pure (MkImport (MkFC fname start end) reexp ns nsAs)

export
prog : FileName -> SourceEmptyRule Module
prog fname
    = do start  <- location
         doc    <- option "" documentation
         nspace <- option ["Main"]
                     (do keyword "module"
                         namespacedIdent)
         end     <- location
         imports <- block (import_ fname)
         ds      <- block (topDecl fname)
         pure (MkModule (MkFC fname start end)
                        nspace imports doc (collectDefs (concat ds)))

export
progHdr : FileName -> SourceEmptyRule Module
progHdr fname
    = do start  <- location
         doc    <- option "" documentation
         nspace <- option ["Main"]
                     (do keyword "module"
                         namespacedIdent)
         end     <- location
         imports <- block (import_ fname)
         pure (MkModule (MkFC fname start end)
                        nspace imports doc [])

parseMode : Rule REPLEval
parseMode
     = do exactIdent "typecheck"
          pure EvalTC
   <|> do exactIdent "tc"
          pure EvalTC
   <|> do exactIdent "normalise"
          pure NormaliseAll
   <|> do exactIdent "normalize" -- oh alright then
          pure NormaliseAll
   <|> do exactIdent "execute"
          pure Execute
   <|> do exactIdent "exec"
          pure Execute

setVarOption : Rule REPLOpt
setVarOption
    = do exactIdent "eval"
         mode <- parseMode
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
  <|> do exactIdent "showtypes"
         pure (ShowTypes set)
  <|> if set then setVarOption else fatalError "Unrecognised option"

replCmd : List String -> Rule ()
replCmd [] = fail "Unrecognised command"
replCmd (c :: cs)
    = exactIdent c
  <|> symbol c
  <|> replCmd cs

export
editCmd : Rule EditCmd
editCmd
    = do replCmd ["typeat"]
         line <- intLit
         col <- intLit
         n <- name
         pure (TypeAt (fromInteger line) (fromInteger col) n)
  <|> do replCmd ["cs"]
         upd <- option False (do symbol "!"; pure True)
         line <- intLit
         col <- intLit
         n <- name
         pure (CaseSplit upd (fromInteger line) (fromInteger col) n)
  <|> do replCmd ["ac"]
         upd <- option False (do symbol "!"; pure True)
         line <- intLit
         n <- name
         pure (AddClause upd (fromInteger line) n)
  <|> do replCmd ["ps", "proofsearch"]
         upd <- option False (do symbol "!"; pure True)
         line <- intLit
         n <- name
         pure (ExprSearch upd (fromInteger line) n [] False)
  <|> do replCmd ["psall"]
         upd <- option False (do symbol "!"; pure True)
         line <- intLit
         n <- name
         pure (ExprSearch upd (fromInteger line) n [] True)
  <|> do replCmd ["gd"]
         upd <- option False (do symbol "!"; pure True)
         line <- intLit
         n <- name
         pure (GenerateDef upd (fromInteger line) n)
  <|> do replCmd ["ml", "makelemma"]
         upd <- option False (do symbol "!"; pure True)
         line <- intLit
         n <- name
         pure (MakeLemma upd (fromInteger line) n)
  <|> do replCmd ["mc", "makecase"]
         upd <- option False (do symbol "!"; pure True)
         line <- intLit
         n <- name
         pure (MakeCase upd (fromInteger line) n)
  <|> do replCmd ["mw", "makewith"]
         upd <- option False (do symbol "!"; pure True)
         line <- intLit
         n <- name
         pure (MakeWith upd (fromInteger line) n)
  <|> fatalError "Unrecognised command"

export
data CmdArg : Type where
     ||| The command takes no arguments.
     NoArg : CmdArg

     ||| The command takes a name.
     NameArg : CmdArg

     ||| The command takes an expression.
     ExprArg : CmdArg

     ||| The command takes a list of declarations
     DeclsArg : CmdArg

     ||| The command takes a number.
     NumberArg : CmdArg

     ||| The command takes an option.
     OptionArg : CmdArg

     ||| The command takes a file.
     FileArg : CmdArg

     ||| The command takes a module.
     ModuleArg : CmdArg

     ||| The command takes multiple arguments.
     Args : List CmdArg -> CmdArg

export
Show CmdArg where
  show NoArg = ""
  show NameArg = "<name>"
  show ExprArg = "<expr>"
  show DeclsArg = "<decls>"
  show NumberArg = "<number>"
  show OptionArg = "<option>"
  show FileArg = "<file>"
  show ModuleArg = "<module>"
  show (Args args) = showSep " " (map show args)

export
data ParseCmd : Type where
     ParseREPLCmd : List String -> ParseCmd
     ParseKeywordCmd : String -> ParseCmd
     ParseIdentCmd : String -> ParseCmd

CommandDefinition : Type
CommandDefinition = (List String, CmdArg, String, Rule REPLCmd)

CommandTable : Type
CommandTable = List CommandDefinition

extractNames : ParseCmd -> List String
extractNames (ParseREPLCmd names) = names
extractNames (ParseKeywordCmd keyword) = [keyword]
extractNames (ParseIdentCmd ident) = [ident]

runParseCmd : ParseCmd -> Rule ()
runParseCmd (ParseREPLCmd names) = replCmd names
runParseCmd (ParseKeywordCmd keyword') = keyword keyword'
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
      n <- name
      pure (command n)

moduleArgCmd : ParseCmd -> (List String -> REPLCmd) -> String -> CommandDefinition
moduleArgCmd parseCmd command doc = (names, ModuleArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      n <- moduleIdent
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
      tm <- expr pdef "(interactive)" init
      pure (command tm)

declsArgCmd : ParseCmd -> (List PDecl -> REPLCmd) -> String -> CommandDefinition
declsArgCmd parseCmd command doc = (names, DeclsArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd
    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      tm <- topDecl "(interactive)" init
      pure (command tm)

optArgCmd : ParseCmd -> (REPLOpt -> REPLCmd) -> Bool -> String -> CommandDefinition
optArgCmd parseCmd command set doc = (names, OptionArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      opt <- setOption set
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
      i <- intLit
      pure (command (fromInteger i))

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
      n <- unqualifiedName
      tm <- expr pdef "(interactive)" init
      pure (command tm n)

parserCommandsForHelp : CommandTable
parserCommandsForHelp =
  [ exprArgCmd (ParseREPLCmd ["t", "type"]) Check "Check the type of an expression"
  , nameArgCmd (ParseREPLCmd ["printdef"]) PrintDef "Show the definition of a function"
  , nameArgCmd (ParseREPLCmd ["s", "search"]) ProofSearch "Search for values by type"
  , nameArgCmd (ParseIdentCmd "di") DebugInfo "Show debugging information for a name"
  , moduleArgCmd (ParseKeywordCmd "module") ImportMod "Import an extra module"
  , noArgCmd (ParseREPLCmd ["q", "quit", "exit"]) Quit "Exit the Idris system"
  , noArgCmd (ParseREPLCmd ["cwd"]) CWD "Displays the current working directory"
  , optArgCmd (ParseIdentCmd "set") SetOpt True "Set an option"
  , optArgCmd (ParseIdentCmd "unset") SetOpt False "Unset an option"
  , compileArgsCmd (ParseREPLCmd ["c", "compile"]) Compile "Compile to an executable"
  , exprArgCmd (ParseIdentCmd "exec") Exec "Compile to an executable and run"
  , noArgCmd (ParseREPLCmd ["r", "reload"]) Reload "Reload current file"
  , noArgCmd (ParseREPLCmd ["e", "edit"]) Edit "Edit current file using $EDITOR or $VISUAL"
  , nameArgCmd (ParseREPLCmd ["miss", "missing"]) Missing "Show missing clauses"
  , nameArgCmd (ParseKeywordCmd "total") Total "Check the totality of a name"
  , nameArgCmd (ParseIdentCmd "doc") Doc "Show documentation for a name"
  , moduleArgCmd (ParseIdentCmd "browse") Browse "Browse contents of a namespace"
  , numberArgCmd (ParseREPLCmd ["log", "logging"]) SetLog "Set logging level"
  , noArgCmd (ParseREPLCmd ["m", "metavars"]) Metavars "Show remaining proof obligations (metavariables or holes)"
  , noArgCmd (ParseREPLCmd ["version"]) ShowVersion "Display the Idris version"
  , noArgCmd (ParseREPLCmd ["?", "h", "help"]) Help "Display this help text"
  , declsArgCmd (ParseKeywordCmd "let") NewDefn "Define a new value"
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
  tm <- expr pdef "(interactive)" init
  pure (Eval tm)

export
command : SourceEmptyRule REPLCmd
command
    = do eoi
         pure NOP
  <|> nonEmptyCommand
  <|> do symbol ":?"; pure Help -- special case, :? doesn't fit into above scheme
  <|> do symbol ":"; cmd <- editCmd
         pure (Editing cmd)
  <|> eval
