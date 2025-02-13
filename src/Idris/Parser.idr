module Idris.Parser

import Core.Options
import Core.Metadata
import Idris.Syntax
import Idris.Syntax.Traversals
import public Parser.Source
import TTImp.TTImp

import public Libraries.Text.Parser
import Data.Either
import Libraries.Data.IMaybe
import Data.List
import Data.List.Quantifiers
import Data.List1
import Data.Maybe
import Data.So
import Data.Nat
import Data.SnocList
import Data.String
import Libraries.Utils.String
import Libraries.Data.WithDefault

import Idris.Parser.Let

%default covering

fcBounds : OriginDesc => Rule a -> Rule (WithFC a)
fcBounds a = (.withFC) <$> bounds a

decorate : {a : Type} -> OriginDesc -> Decoration -> Rule a -> Rule a
decorate fname decor rule = do
  res <- bounds rule
  actD (decorationFromBounded fname decor res)
  pure res.val

dependentDecorate : {a : Type} -> OriginDesc -> Rule a -> (a -> Decoration) -> Rule a
dependentDecorate fname rule decor = do
  res <- bounds rule
  actD (decorationFromBounded fname (decor res.val) res)
  pure res.val

decoratedKeyword : OriginDesc -> String -> Rule ()
decoratedKeyword fname kwd = decorate fname Keyword (keyword kwd)

decorateKeywords : {a : Type} -> OriginDesc -> List (WithBounds a) -> EmptyRule ()
decorateKeywords fname xs
  = act $ MkState (cast (map (decorationFromBounded fname Keyword) xs)) []

decoratedPragma : OriginDesc -> String -> Rule ()
decoratedPragma fname prg = decorate fname Keyword (pragma prg)

decoratedSymbol : OriginDesc -> String -> Rule ()
decoratedSymbol fname smb = decorate fname Keyword (symbol smb)

decoratedNamespacedSymbol : OriginDesc -> String -> Rule (Maybe Namespace)
decoratedNamespacedSymbol fname smb =
  decorate fname Keyword $ namespacedSymbol smb

parens : {b : _} -> OriginDesc -> BRule b a -> Rule a
parens fname p
  = pure id <* decoratedSymbol fname "("
            <*> p
            <* decoratedSymbol fname ")"

curly : {b : _} -> OriginDesc -> BRule b a -> Rule a
curly fname p
  = pure id <* decoratedSymbol fname "{"
            <*> p
            <* decoratedSymbol fname "}"

decoratedDataTypeName : OriginDesc -> Rule Name
decoratedDataTypeName fname = decorate fname Typ dataTypeName

decoratedDataConstructorName : OriginDesc -> Rule Name
decoratedDataConstructorName fname = decorate fname Data dataConstructorName

decoratedSimpleBinderUName : OriginDesc -> Rule Name
decoratedSimpleBinderUName fname = decorate fname Bound (UN . Basic <$> unqualifiedName)

decoratedSimpleNamedArg : OriginDesc -> Rule String
decoratedSimpleNamedArg fname
  = decorate fname Bound unqualifiedName
  <|> parens fname (decorate fname Bound unqualifiedOperatorName)

-- Forward declare since they're used in the parser
topDecl : OriginDesc -> IndentInfo -> Rule PDecl
collectDefs : List PDecl -> List PDecl

-- Some context for the parser
public export
record ParseOpts where
  constructor MkParseOpts
  eqOK : Bool -- = operator is parseable
  withOK : Bool -- = with applications are parseable

peq : ParseOpts -> ParseOpts
peq = { eqOK := True }

pnoeq : ParseOpts -> ParseOpts
pnoeq = { eqOK := False }

export
pdef : ParseOpts
pdef = MkParseOpts {eqOK = True, withOK = True}

pnowith : ParseOpts
pnowith = MkParseOpts {eqOK = True, withOK = False}

export
plhs : ParseOpts
plhs = MkParseOpts {eqOK = False, withOK = False}

%hide Prelude.(>>)
%hide Prelude.(>>=)
%hide Core.Core.(>>)
%hide Core.Core.(>>=)
%hide Prelude.pure
%hide Core.Core.pure
%hide Prelude.(<*>)
%hide Core.Core.(<*>)

atom : OriginDesc -> Rule PTerm
atom fname
    = do x <- bounds $ decorate fname Typ $ exactIdent "Type"
         pure (PType (boundToFC fname x))
  <|> do x <- bounds $ name
         pure (PRef (boundToFC fname x) x.val)
  <|> do x <- bounds $ dependentDecorate fname constant $ \c =>
                       if isPrimType c
                       then Typ
                       else Data
         pure (PPrimVal (boundToFC fname x) x.val)
  <|> do x <- bounds $ decoratedSymbol fname "_"
         pure (PImplicit (boundToFC fname x))
  <|> do x <- bounds $ symbol "?"
         pure (PInfer (boundToFC fname x))
  <|> do x <- bounds $ holeName
         actH x.val -- record the hole name in the parser
         pure (PHole (boundToFC fname x) False x.val)
  <|> do x <- bounds $ decorate fname Data $ pragma "MkWorld"
         pure (PPrimVal (boundToFC fname x) WorldVal)
  <|> do x <- bounds $ decorate fname Typ  $ pragma "World"
         pure (PPrimVal (boundToFC fname x) $ PrT WorldType)
  <|> do x <- bounds $ decoratedPragma fname "search"
         pure (PSearch (boundToFC fname x) 50)

whereBlock : OriginDesc -> Int -> Rule (List PDecl)
whereBlock fname col
    = do decoratedKeyword fname "where"
         ds <- blockAfter col (topDecl fname)
         pure (collectDefs ds)

-- Expect a keyword, but if we get anything else it's a fatal error
commitKeyword : OriginDesc -> IndentInfo -> String -> Rule ()
commitKeyword fname indents req
    = do mustContinue indents (Just req)
         decoratedKeyword fname req
          <|> the (Rule ()) (fatalError ("Expected '" ++ req ++ "'"))
         mustContinue indents Nothing

commitSymbol : OriginDesc -> String -> Rule ()
commitSymbol fname req
    = decoratedSymbol fname req
       <|> fatalError ("Expected '" ++ req ++ "'")

continueWithDecorated : OriginDesc -> IndentInfo -> String -> Rule ()
continueWithDecorated fname indents req
    = mustContinue indents (Just req) *> decoratedSymbol fname req


continueWith : IndentInfo -> String -> Rule ()
continueWith indents req
    = mustContinue indents (Just req) *> symbol req

iOperator : Rule OpStr
iOperator
    = OpSymbols <$> operator
  <|> Backticked <$> (symbol "`" *> name <* symbol "`")

data ArgType
    = UnnamedExpArg PTerm
    | UnnamedAutoArg PTerm
    | NamedArg Name PTerm
    | WithArg PTerm

argTerm : ArgType -> PTerm
argTerm (UnnamedExpArg t) = t
argTerm (UnnamedAutoArg t) = t
argTerm (NamedArg _ t) = t
argTerm (WithArg t) = t

export
debugString : OriginDesc -> Rule PTerm
debugString fname = do
  di <- bounds debugInfo
  pure $ PPrimVal (boundToFC fname di) $ Str $ case di.val of
    DebugLoc =>
      let bnds = di.bounds in
      joinBy ", "
      [ "File \{show fname}"
      , "line \{show (startLine bnds)}"
      , "characters \{show (startCol bnds)}\{
           ifThenElse (startLine bnds == endLine bnds)
            ("-\{show (endCol bnds)}")
            ""
        }"
      ]
    DebugFile => "\{show fname}"
    DebugLine => "\{show (startLine di.bounds)}"
    DebugCol => "\{show (startCol di.bounds)}"

totalityOpt : OriginDesc -> Rule TotalReq
totalityOpt fname
    = (decoratedKeyword fname "partial" $> PartialOK)
  <|> (decoratedKeyword fname "total" $> Total)
  <|> (decoratedKeyword fname "covering" $> CoveringOnly)

fnOpt : OriginDesc -> Rule PFnOpt
fnOpt fname
      = do x <- totalityOpt fname
           pure $ IFnOpt (Totality x)

mutual
  appExpr : ParseOpts -> OriginDesc -> IndentInfo -> Rule PTerm
  appExpr q fname indents
      = case_ fname indents
    <|> doBlock fname indents
    <|> lam fname indents
    <|> lazy fname indents
    <|> if_ fname indents
    <|> with_ fname indents
    <|> do b <- bounds (MkPair <$> simpleExpr fname indents <*> many (argExpr q fname indents))
           (f, args) <- pure b.val
           pure (applyExpImp (start b) (end b) f (concat args))
    <|> do b <- fcBounds (MkPair <$> fcBounds iOperator <*> expr pdef fname indents)
           (op, arg) <- pure b.val
           pure (PPrefixOp b.fc op arg)
    <|> fail "Expected 'case', 'if', 'do', application or operator expression"
    where
      applyExpImp : FilePos -> FilePos -> PTerm ->
                    List ArgType ->
                    PTerm
      applyExpImp start end f [] = f
      applyExpImp start end f (UnnamedExpArg exp :: args)
          = applyExpImp start end (PApp (MkFC fname start end) f exp) args
      applyExpImp start end f (UnnamedAutoArg imp :: args)
          = applyExpImp start end (PAutoApp (MkFC fname start end) f imp) args
      applyExpImp start end f (NamedArg n imp :: args)
          = let fc = MkFC fname start end in
            applyExpImp start end (PNamedApp fc f n imp) args
      applyExpImp start end f (WithArg exp :: args)
          = applyExpImp start end (PWithApp (MkFC fname start end) f exp) args

  argExpr : ParseOpts -> OriginDesc -> IndentInfo -> Rule (List ArgType)
  argExpr q fname indents
      = do continue indents
           arg <- simpleExpr fname indents
           the (EmptyRule _) $ case arg of
                PHole loc _ n => pure [UnnamedExpArg (PHole loc True n)]
                t => pure [UnnamedExpArg t]
    <|> do continue indents
           braceArgs fname indents
    <|> if withOK q
           then do continue indents
                   decoratedSymbol fname "|"
                   arg <- expr ({withOK := False} q) fname indents
                   pure [WithArg arg]
           else fail "| not allowed here"
    where
      underscore : FC -> ArgType
      underscore fc = NamedArg (UN Underscore) (PImplicit fc)

      braceArgs : OriginDesc -> IndentInfo -> Rule (List ArgType)
      braceArgs fname indents
        = do start <- bounds (decoratedSymbol fname "{")
             mustWork $ do
               list <- sepBy (decoratedSymbol fname ",")
                        $ do x <- bounds (UN . Basic <$> decoratedSimpleNamedArg fname)
                             let fc = boundToFC fname x
                             option (NamedArg x.val $ PRef fc x.val)
                              $ do tm <- decoratedSymbol fname "=" *> typeExpr pdef fname indents
                                   pure (NamedArg x.val tm)
               matchAny <- option [] (if isCons list then
                                         do decoratedSymbol fname ","
                                            x <- bounds (decoratedSymbol fname "_")
                                            pure [underscore (boundToFC fname x)]
                                      else fail "non-empty list required")
               end <- bounds (decoratedSymbol fname "}")
               matchAny <- do let fc = boundToFC fname (mergeBounds start end)
                              pure $ if isNil list
                                then [underscore fc]
                                else matchAny
               pure $ matchAny ++ list

        <|> do decoratedSymbol fname "@{"
               commit
               tm <- typeExpr pdef fname indents
               decoratedSymbol fname "}"
               pure [UnnamedAutoArg tm]

  with_ : OriginDesc -> IndentInfo -> Rule PTerm
  with_ fname indents
      = do b <- bounds (do decoratedKeyword fname "with"
                           commit
                           ns <- singleName <|> nameList
                           end <- location
                           rhs <- expr pdef fname indents
                           pure (ns, rhs))
           (ns, rhs) <- pure b.val
           pure (PWithUnambigNames (boundToFC fname b) ns rhs)
    where
      singleName : Rule (List (FC, Name))
      singleName = do
        n <- bounds name
        pure [(boundToFC fname n, n.val)]

      nameList : Rule (List (FC, Name))
      nameList = do
        decoratedSymbol fname "["
        commit
        ns <- sepBy1 (decoratedSymbol fname ",") (bounds name)
        decoratedSymbol fname "]"
        pure (map (\ n => (boundToFC fname n, n.val)) $ forget ns)

  -- The different kinds of operator bindings `x : ty` for typebind
  -- x := e and x : ty := e for autobind
  opBinderTypes : OriginDesc -> IndentInfo -> WithBounds PTerm -> Rule (OperatorLHSInfo PTerm)
  opBinderTypes fname indents boundName =
           do decoratedSymbol fname ":"
              ty <- typeExpr pdef fname indents
              decoratedSymbol fname ":="
              exp <- expr pdef fname indents
              pure (BindExplicitType boundName.val ty exp)
       <|> do decoratedSymbol fname ":="
              exp <- expr pdef fname indents
              pure (BindExpr boundName.val exp)
       <|> do decoratedSymbol fname ":"
              ty <- typeExpr pdef fname indents
              pure (BindType boundName.val ty)

  opBinder : OriginDesc -> IndentInfo -> Rule (OperatorLHSInfo PTerm)
  opBinder fname indents
      = do boundName <- bounds (expr plhs fname indents)
           opBinderTypes fname indents boundName

  autobindOp : ParseOpts -> OriginDesc -> IndentInfo -> Rule PTerm
  autobindOp q fname indents
      = do b <- fcBounds $ do
             binder <- fcBounds $ parens fname (opBinder fname indents)
             continue indents
             op <- fcBounds iOperator
             commit
             e <- expr q fname indents
             pure (binder, op, e)
           pure (POp b.fc (fst b.val) (fst (snd b.val)) (snd (snd b.val)))

  opExprBase : ParseOpts -> OriginDesc -> IndentInfo -> Rule PTerm
  opExprBase q fname indents
      = do l <- bounds (appExpr q fname indents)
           (if eqOK q
               then do r <- bounds (continue indents
                                *> decoratedSymbol fname "="
                                *> opExprBase q fname indents)
                       pure $
                         let fc = boundToFC fname (mergeBounds l r)
                             opFC = virtualiseFC fc -- already been highlighted: we don't care
                         in POp fc (mapFC NoBinder l.withFC)
                                   (MkFCVal opFC (OpSymbols $ UN $ Basic "="))
                                   r.val
               else fail "= not allowed")
             <|>
             (do b <- bounds $ do
                        continue indents
                        op <- fcBounds iOperator
                        e <- case op.val of
                               OpSymbols (UN (Basic "$")) => typeExpr q fname indents
                               _ => expr q fname indents
                        pure (op, e)
                 (op, r) <- pure b.val
                 let fc = boundToFC fname (mergeBounds l b)
                 pure (POp fc (mapFC NoBinder l.withFC) op r))
               <|> pure l.val

  opExpr : ParseOpts -> OriginDesc -> IndentInfo -> Rule PTerm
  opExpr q fname indents = autobindOp q fname indents
                       <|> opExprBase q fname indents

  dpairType : OriginDesc -> WithBounds t -> IndentInfo -> Rule PTerm
  dpairType fname start indents
      = do loc <- bounds (do x <- decoratedSimpleBinderUName fname
                             decoratedSymbol fname ":"
                             ty <- typeExpr pdef fname indents
                             pure (x, ty))
           (x, ty) <- pure loc.val
           op <- bounds (symbol "**")
           rest <- bounds (nestedDpair fname loc indents <|> typeExpr pdef fname indents)
           pure (PDPair (boundToFC fname (mergeBounds start rest))
                        (boundToFC fname op)
                        (PRef (boundToFC fname loc) x)
                        ty
                        rest.val)

  nestedDpair : OriginDesc -> WithBounds t -> IndentInfo -> Rule PTerm
  nestedDpair fname start indents
      = dpairType fname start indents
    <|> do l <- expr pdef fname indents
           loc <- bounds (symbol "**")
           rest <- bounds (nestedDpair fname loc indents <|> expr pdef fname indents)
           pure (PDPair (boundToFC fname (mergeBounds start rest))
                        (boundToFC fname loc)
                        l
                        (PImplicit (boundToFC fname (mergeBounds start rest)))
                        rest.val)

  bracketedExpr : OriginDesc -> WithBounds t -> IndentInfo -> Rule PTerm
  bracketedExpr fname s indents
      -- left section. This may also be a prefix operator, but we'll sort
      -- that out when desugaring: if the operator is infix, treat it as a
      -- section otherwise treat it as prefix
      = do b <- bounds (do op <- fcBounds iOperator
                           e <- expr pdef fname indents
                           continueWithDecorated fname indents ")"
                           pure (op, e))
           (op, e) <- pure b.val
           actD (toNonEmptyFC $ boundToFC fname s, Keyword, Nothing)
           let fc = boundToFC fname (mergeBounds s b)
           pure (PSectionL fc op e)
    <|> do  -- (.y.z)  -- section of projection (chain)
           b <- bounds $ forget <$> some (bounds postfixProj)
           decoratedSymbol fname ")"
           actD (toNonEmptyFC $ boundToFC fname s, Keyword, Nothing)
           let projs = map (\ proj => (boundToFC fname proj, proj.val)) b.val
           pure $ PPostfixAppPartial (boundToFC fname b) projs
      -- unit type/value
    <|> do b <- bounds (continueWith indents ")")
           pure (PUnit (boundToFC fname (mergeBounds s b)))
      -- dependent pairs with type annotation (so, the type form)
    <|> do dpairType fname s indents <* (decorate fname Typ $ symbol ")")
                                     <* actD (toNonEmptyFC $ boundToFC fname s, Typ, Nothing)
    <|> do e <- bounds (typeExpr pdef fname indents)
           -- dependent pairs with no type annotation
           (do loc <- bounds (symbol "**")
               rest <- bounds ((nestedDpair fname loc indents <|> expr pdef fname indents) <* symbol ")")
               pure (PDPair (boundToFC fname (mergeBounds s rest))
                            (boundToFC fname loc)
                            e.val
                            (PImplicit (boundToFC fname (mergeBounds s rest)))
                            rest.val)) <|>
             -- right sections
             ((do op <- bounds (fcBounds iOperator <* decoratedSymbol fname ")")
                  actD (toNonEmptyFC $ boundToFC fname s, Keyword, Nothing)
                  let fc = boundToFC fname (mergeBounds s op)
                  pure (PSectionR fc e.val op.val)
               <|>
              -- all the other bracketed expressions
              tuple fname s indents e.val))
    <|> do here <- location
           let fc = MkFC fname here here
           let var = PRef fc (MN "__leftTupleSection" 0)
           ts <- bounds (nonEmptyTuple fname s indents var)
           pure (PLam fc top Explicit var (PInfer fc) ts.val)

  getInitRange : List (WithBounds PTerm) -> EmptyRule (PTerm, Maybe PTerm)
  getInitRange [x] = pure (x.val, Nothing)
  getInitRange [x,y] = pure (x.val, Just y.val)
  getInitRange _ = fatalError "Invalid list range syntax"

  listRange : OriginDesc -> WithBounds t -> IndentInfo -> List (WithBounds PTerm) -> Rule PTerm
  listRange fname s indents xs
      = do b <- bounds (decoratedSymbol fname "]")
           let fc = boundToFC fname (mergeBounds s b)
           rstate <- getInitRange xs
           decorateKeywords fname xs
           pure (PRangeStream fc (fst rstate) (snd rstate))
    <|> do y <- bounds (expr pdef fname indents <* decoratedSymbol fname "]")
           let fc = boundToFC fname (mergeBounds s y)
           rstate <- getInitRange xs
           decorateKeywords fname xs
           pure (PRange fc (fst rstate) (snd rstate) y.val)

  listExpr : OriginDesc -> WithBounds () -> IndentInfo -> Rule PTerm
  listExpr fname s indents
      = do b <- bounds (do ret <- expr pnowith fname indents
                           decoratedSymbol fname "|"
                           conds <- sepBy1 (decoratedSymbol fname ",") (doAct fname indents)
                           decoratedSymbol fname "]"
                           pure (ret, conds))
           (ret, conds) <- pure b.val
           pure (PComprehension (boundToFC fname (mergeBounds s b)) ret (concat conds))
    <|> do xs <- option [] $ do
                     hd <- expr pdef fname indents
                     tl <- many $ do b <- bounds (symbol ",")
                                     x <- mustWork $ expr pdef fname indents
                                     pure (x <$ b)
                     pure ((hd <$ s) :: tl)
           (do decoratedSymbol fname ".."
               listRange fname s indents xs)
             <|> (do b <- bounds (symbol "]")
                     pure $
                       let fc = boundToFC fname (mergeBounds s b)
                           nilFC = if null xs then fc else boundToFC fname b
                       in PList fc nilFC (cast (map (\ t => (boundToFC fname t, t.val)) xs)))

  snocListExpr : OriginDesc -> WithBounds () -> IndentInfo -> Rule PTerm
  snocListExpr fname s indents
      = {- TODO: comprehension -}
        do mHeadTail <- optional $ do
             hd <- many $ do x <- expr pdef fname indents
                             b <- bounds (symbol ",")
                             pure (x <$ b)
             tl <- expr pdef fname indents
             pure (hd, tl)
           {- TODO: reverse ranges -}
           b <- bounds (symbol "]")
           pure $
             let xs : SnocList (WithBounds PTerm)
                    = case mHeadTail of
                        Nothing      => [<]
                        Just (hd,tl) => ([<] <>< hd) :< (tl <$ b)
                 fc = boundToFC fname (mergeBounds s b)
                 nilFC = ifThenElse (null xs) fc (boundToFC fname s)
             in PSnocList fc nilFC (map (\ t => (boundToFC fname t, t.val)) xs) --)

  nonEmptyTuple : OriginDesc -> WithBounds t -> IndentInfo -> PTerm -> Rule PTerm
  nonEmptyTuple fname s indents e
      = do vals <- some $ do b <- bounds (symbol ",")
                             exp <- optional (typeExpr pdef fname indents)
                             pure (boundToFC fname b, exp)
           end <- continueWithDecorated fname indents ")"
           actD (toNonEmptyFC (boundToFC fname s), Keyword, Nothing)
           pure $ let (start ::: rest) = vals in
                  buildOutput (fst start) (mergePairs 0 start rest)
    where

      lams : List (FC, PTerm) -> PTerm -> PTerm
      lams [] e = e
      lams ((fc, var) :: vars) e
        = let vfc = virtualiseFC fc in
          PLam vfc top Explicit var (PInfer vfc) $ lams vars e

      buildOutput : FC -> (List (FC, PTerm), PTerm) -> PTerm
      buildOutput fc (vars, scope) = lams vars $ PPair fc e scope

      optionalPair : Int ->
                     (FC, Maybe PTerm) -> (Int, (List (FC, PTerm), PTerm))
      optionalPair i (fc, Just e)  = (i, ([], e))
      optionalPair i (fc, Nothing) =
        let var = PRef fc (MN "__infixTupleSection" i) in
        (i+1, ([(fc, var)], var))

      mergePairs : Int -> (FC, Maybe PTerm) ->
                   List (FC, Maybe PTerm) -> (List (FC, PTerm), PTerm)
      mergePairs i hd [] = snd (optionalPair i hd)
      mergePairs i hd (exp :: rest)
          = let (j, (var, t)) = optionalPair i hd in
            let (vars, ts)    = mergePairs j exp rest in
            (var ++ vars, PPair (fst exp) t ts)

  -- A pair, dependent pair, or just a single expression
  tuple : OriginDesc -> WithBounds t -> IndentInfo -> PTerm -> Rule PTerm
  tuple fname s indents e
     =   nonEmptyTuple fname s indents e
     <|> do end <- bounds (continueWithDecorated fname indents ")")
            actD (toNonEmptyFC $ boundToFC fname s, Keyword, Nothing)
            pure (PBracketed (boundToFC fname (mergeBounds s end)) e)

  simpleExpr : OriginDesc -> IndentInfo -> Rule PTerm
  simpleExpr fname indents
    = do  -- x.y.z
          b <- bounds (do root <- simplerExpr fname indents
                          projs <- many (bounds postfixProj)
                          pure (root, projs))
          (root, projs) <- pure b.val
          let projs = map (\ proj => (boundToFC fname proj, proj.val)) projs
          pure $ case projs of
            [] => root
            _  => PPostfixApp (boundToFC fname b) root projs
    <|> debugString fname
    <|> do b <- bounds (forget <$> some (bounds postfixProj))
           pure $ let projs = map (\ proj => (boundToFC fname proj, proj.val)) b.val in
                  PPostfixAppPartial (boundToFC fname b) projs

  simplerExpr : OriginDesc -> IndentInfo -> Rule PTerm
  simplerExpr fname indents
      = do b <- bounds (do x <- bounds (decoratedSimpleBinderUName fname)
                           decoratedSymbol fname "@"
                           commit
                           expr <- simpleExpr fname indents
                           pure (x, expr))
           (x, expr) <- pure b.val
           pure (PAs (boundToFC fname b) (boundToFC fname x) x.val expr)
    <|> do b <- bounds $ do
                  mns <- decoratedNamespacedSymbol fname "[|"
                  t   <- expr pdef fname indents
                  decoratedSymbol fname "|]"
                  pure (t, mns)
           pure (PIdiom (boundToFC fname b) (snd b.val) (fst b.val))
    <|> atom fname
    <|> record_ fname indents
    <|> singlelineStr pdef fname indents
    <|> multilineStr pdef fname indents
    <|> do b <- bounds $ do
                  decoratedSymbol fname ".("
                  commit
                  t <- typeExpr pdef fname indents
                  decoratedSymbol fname ")"
                  pure t
           pure (PDotted (boundToFC fname b) b.val)
    <|> do b <- bounds $ do
                  decoratedSymbol fname "`("
                  t <- typeExpr pdef fname indents
                  decoratedSymbol fname ")"
                  pure t
           pure (PQuote (boundToFC fname b) b.val)
    <|> do b <- bounds $ do
                  decoratedSymbol fname "`{"
                  t <- name
                  decoratedSymbol fname "}"
                  pure t
           pure (PQuoteName (boundToFC fname b) b.val)
    <|> do b <- bounds $ do
                  decoratedSymbol fname "`["
                  ts <- nonEmptyBlock (topDecl fname)
                  decoratedSymbol fname "]"
                  pure ts
           pure (PQuoteDecl (boundToFC fname b) (collectDefs (forget b.val)))
    <|> do b <- bounds (decoratedSymbol fname "~" *> simplerExpr fname indents)
           pure (PUnquote (boundToFC fname b) b.val)
    <|> do start <- bounds (symbol "(")
           bracketedExpr fname start indents
    <|> do start <- bounds (symbol "[<")
           snocListExpr fname start indents
    <|> do start <- bounds (symbol "[>" <|> symbol "[")
           listExpr fname start indents
    <|> do b <- bounds (decoratedSymbol fname "!" *> simpleExpr fname indents)
           pure (PBang (virtualiseFC $ boundToFC fname b) b.val)
    <|> do b <- bounds $ do decoratedPragma fname "logging"
                            topic <- optional (split (('.') ==) <$> simpleStr)
                            lvl   <- intLit
                            e     <- expr pdef fname indents
                            pure (MkPair (mkLogLevel' topic (integerToNat lvl)) e)
           (lvl, e) <- pure b.val
           pure (PUnifyLog (boundToFC fname b) lvl e)
    <|> withWarning "DEPRECATED: trailing lambda. Use a $ or parens"
        (lam fname indents)

  multiplicity : OriginDesc -> EmptyRule RigCount
  multiplicity fname
      = case !(optional $ decorate fname Keyword intLit) of
          (Just 0) => pure erased
          (Just 1) => pure linear
          Nothing => pure top
          _ => fail "Invalid multiplicity (must be 0 or 1)"

  bindList : OriginDesc -> IndentInfo ->
             Rule (List (RigCount, WithBounds PTerm, PTerm))
  bindList fname indents
      = forget <$> sepBy1 (decoratedSymbol fname ",")
                          (do rig <- multiplicity fname
                              pat <- bounds (simpleExpr fname indents)
                              ty <- option
                                       (PInfer (boundToFC fname pat))
                                       (decoratedSymbol fname ":" *> opExpr pdef fname indents)
                              pure (rig, pat, ty))

  ||| A list of names bound to the same type
  ||| BNF:
  ||| pibindListName := qty name (, name)* ':' typeExpr
  pibindListName : OriginDesc -> IndentInfo ->
                   Rule BasicMultiBinder
  pibindListName fname indents
       = do rig <- multiplicity fname
            ns <- sepBy1 (decoratedSymbol fname ",")
                         (fcBounds binderName)
            decoratedSymbol fname ":"
            ty <- typeExpr pdef fname indents
            atEnd indents
            pure (MkBasicMultiBinder rig ns ty)
    where
      -- _ gets treated specially here, it means "I don't care about the name"
      binderName : Rule Name
      binderName = decoratedSimpleBinderUName fname
               <|> decorate fname Bound (UN <$> symbol "_" $> Underscore)

  ||| The arrow used after an explicit binder
  ||| BNF:
  ||| bindSymbol := '->' | '=>'
  bindSymbol : OriginDesc -> Rule (PiInfo PTerm)
  bindSymbol fname
      = (decoratedSymbol fname "->" $> Explicit)
    <|> (decoratedSymbol fname "=>" $> AutoImplicit)

  ||| An explicit pi-type
  ||| BNF:
  ||| explicitPi := '(' pibindListName ')' bindSymbol typeExpr
  explicitPi : OriginDesc -> IndentInfo -> Rule PTerm
  explicitPi fname indents
      = NewPi <$> fcBounds (do
           b <- bounds $ parens fname $ pibindListName fname indents
           exp <- mustWorkBecause b.bounds "Cannot return a named argument"
                    $ bindSymbol fname
           scope <- mustWork $ typeExpr pdef fname indents
           pure (MkPBinderScope (MkPBinder exp b.val) scope))

  ||| An auto-implicit pi-type
  ||| BNF:
  ||| autoImplicitPi := '{' 'auto' pibindListName '}' '->' typeExpr
  autoImplicitPi : OriginDesc -> IndentInfo -> Rule PTerm
  autoImplicitPi fname indents
      = NewPi <$> fcBounds (do
           b <- bounds $ curly fname $ do
                  decoratedKeyword fname "auto"
                  commit
                  binders <- pibindListName fname indents
                  pure binders
           mustWorkBecause b.bounds "Cannot return an auto implicit argument"
             $ decoratedSymbol fname "->"
           scope <- mustWork $ typeExpr pdef fname indents
           pure (MkPBinderScope (MkPBinder AutoImplicit b.val) scope)
           )

  ||| An default implicit pi-type
  ||| BNF:
  ||| defaultImplicitPi := '{' 'default' simpleExpr pibindListName '}' '->' typeExpr
  defaultImplicitPi : OriginDesc -> IndentInfo -> Rule PTerm
  defaultImplicitPi fname indents
      = NewPi <$> fcBounds (do
           b <- bounds $ curly fname $ do
                  decoratedKeyword fname "default"
                  commit
                  t <- simpleExpr fname indents
                  binders <- pibindListName fname indents
                  pure (MkPBinder (DefImplicit t) binders)
           mustWorkBecause b.bounds "Cannot return a default implicit argument"
             $ decoratedSymbol fname "->"
           scope <- mustWork $ typeExpr pdef fname indents
           pure (MkPBinderScope b.val scope)
           )

  ||| Forall definition that automatically binds the names
  ||| BNF:
  ||| forall_ := 'forall' name (, name)* '.' typeExpr
  forall_ : OriginDesc -> IndentInfo -> Rule PTerm
  forall_ fname indents
      = Forall <$> fcBounds (do
           b <- bounds $ do
                  decoratedKeyword fname "forall"
                  commit
                  ns <- sepBy1 (decoratedSymbol fname ",")
                               (fcBounds (decoratedSimpleBinderUName fname))
                  pure ns
           b' <- bounds peek
           mustWorkBecause b'.bounds "Expected ',' or '.'"
             $ decoratedSymbol fname "."
           scope <- mustWork $ typeExpr pdef fname indents
           pure (b.val, scope))

  ||| implicit pi-type
  ||| BNF:
  ||| implicitPi := '{' pibindListName '}' '->' typeExpr
  implicitPi : OriginDesc -> IndentInfo -> Rule PTerm
  implicitPi fname indents
      = NewPi <$> fcBounds (do
           b <- bounds $ curly fname $ pibindListName fname indents
           mustWorkBecause b.bounds "Cannot return an implicit argument"
            $ decoratedSymbol fname "->"
           scope <- mustWork $ typeExpr pdef fname indents
           pure (MkPBinderScope (MkPBinder Implicit b.val) scope)
           )

  lam : OriginDesc -> IndentInfo -> Rule PTerm
  lam fname indents
      = do decoratedSymbol fname "\\"
           commit
           switch <- optional (bounds $ decoratedKeyword fname "case")
           case switch of
             Nothing => continueLamImpossible <|> continueLam
             Just r  => continueLamCase r

     where
       continueLamImpossible : Rule PTerm
       continueLamImpossible = do
           lhs <- bounds (opExpr plhs fname indents)
           end <- bounds (decoratedKeyword fname "impossible")
           pure (
             let fc = boundToFC fname (mergeBounds lhs end)
                 alt = (MkImpossible fc lhs.val)
                 fcCase = boundToFC fname lhs
                 n = MN "lcase" 0 in
             (PLam fcCase top Explicit (PRef fcCase n) (PInfer fcCase) $
                 PCase (virtualiseFC fc) [] (PRef fcCase n) [alt]))

       bindAll : List (RigCount, WithBounds PTerm, PTerm) -> PTerm -> PTerm
       bindAll [] scope = scope
       bindAll ((rig, pat, ty) :: rest) scope
           = PLam (boundToFC fname pat) rig Explicit pat.val ty
                  (bindAll rest scope)

       continueLam : Rule PTerm
       continueLam = do
           binders <- bindList fname indents
           commitSymbol fname "=>"
           mustContinue indents Nothing
           scope <- typeExpr pdef fname indents
           pure (bindAll binders scope)

       continueLamCase : WithBounds () -> Rule PTerm
       continueLamCase endCase = do
           b <- bounds (forget <$> nonEmptyBlock (caseAlt fname))
           pure
            (let fc = boundToFC fname b
                 fcCase = virtualiseFC $ boundToFC fname endCase
                 n = MN "lcase" 0 in
              PLam fcCase top Explicit (PRef fcCase n) (PInfer fcCase) $
                PCase (virtualiseFC fc) [] (PRef fcCase n) b.val)

  letBlock : OriginDesc -> IndentInfo -> Rule (WithBounds (Either LetBinder LetDecl))
  letBlock fname indents = bounds (letBinder <||> letDecl) where

    letBinder : Rule LetBinder
    letBinder = do s <- bounds (MkPair <$> multiplicity fname <*> expr plhs fname indents)
                   (rig, pat) <- pure s.val
                   ty <- option (PImplicit (virtualiseFC $ boundToFC fname s))
                                (decoratedSymbol fname ":" *> typeExpr (pnoeq pdef) fname indents)
                   (decoratedSymbol fname "=" <|> decoratedSymbol fname ":=")
                   val <- typeExpr pnowith fname indents
                   alts <- block (patAlt fname)
                   pure (MkLetBinder rig pat ty val alts)

    letDecl : Rule LetDecl
    letDecl = collectDefs . forget <$> nonEmptyBlock (try . topDecl fname)

  let_ : OriginDesc -> IndentInfo -> Rule PTerm
  let_ fname indents
      = do decoratedKeyword fname "let"
           commit
           res <- nonEmptyBlock (letBlock fname)
           commitKeyword fname indents "in"
           scope <- typeExpr pdef fname indents
           pure (mkLets fname res scope)

  case_ : OriginDesc -> IndentInfo -> Rule PTerm
  case_ fname indents
      = do opts <- many (fnDirectOpt fname)
           b <- bounds (do decoratedKeyword fname "case"
                           scr <- expr pdef fname indents
                           mustWork (commitKeyword fname indents "of")
                           alts <- block (caseAlt fname)
                           pure (scr, alts))
           (scr, alts) <- pure b.val
           pure (PCase (virtualiseFC $ boundToFC fname b) opts scr alts)


  caseAlt : OriginDesc -> IndentInfo -> Rule PClause
  caseAlt fname indents
      = do lhs <- bounds (opExpr plhs fname indents)
           caseRHS fname lhs indents lhs.val

  caseRHS : OriginDesc -> WithBounds t -> IndentInfo -> PTerm -> Rule PClause
  caseRHS fname start indents lhs
      = do rhs <- bounds $ do
                    decoratedSymbol fname "=>"
                    mustContinue indents Nothing
                    typeExpr pdef fname indents
           atEnd indents
           let fc = boundToFC fname (mergeBounds start rhs)
           pure (MkPatClause fc lhs rhs.val [])
    <|> do end <- bounds (decoratedKeyword fname "impossible")
           atEnd indents
           pure (MkImpossible (boundToFC fname (mergeBounds start end)) lhs)
    <|> fatalError ("Expected '=>' or 'impossible'")

  if_ : OriginDesc -> IndentInfo -> Rule PTerm
  if_ fname indents
      = do b <- bounds (do decoratedKeyword fname "if"
                           commit
                           x <- expr pdef fname indents
                           commitKeyword fname indents "then"
                           t <- typeExpr pdef fname indents
                           commitKeyword fname indents "else"
                           e <- typeExpr pdef fname indents
                           pure (x, t, e))
           mustWork $ atEnd indents
           (x, t, e) <- pure b.val
           pure (PIfThenElse (boundToFC fname b) x t e)

  record_ : OriginDesc -> IndentInfo -> Rule PTerm
  record_ fname indents
      = do
           b <- (
               withWarning oldSyntaxWarning (
                 bounds (do
                   decoratedKeyword fname "record"
                   commit
                   body True
                 ))
             <|>
               bounds (body False))
           pure (PUpdate (boundToFC fname b) (forget b.val))
    where
      oldSyntaxWarning : String
      oldSyntaxWarning = unlines
        [ "DEPRECATED: old record update syntax."
        , #"  Use "{ f := v } p" instead of "record { f = v } p""#
        , #"  and "{ f $= v } p" instead of "record { f $= v } p""#
        ]

      body : Bool -> Rule (List1 PFieldUpdate)
      body kw = curly fname $ do
        commit
        sepBy1 (decoratedSymbol fname ",") (field kw fname indents)

  field : Bool -> OriginDesc -> IndentInfo -> Rule PFieldUpdate
  field kw fname indents
      = do path <- map fieldName <$> [| decorate fname Function name :: many recFieldCompat |]
           upd <- (ifThenElse kw (decoratedSymbol fname "=") (decoratedSymbol fname ":=") $> PSetField)
                      <|>
                  (decoratedSymbol fname "$=" $> PSetFieldApp)
           val <- typeExpr plhs fname indents
           pure (upd path val)
    where
      fieldName : Name -> String
      fieldName (UN (Basic s)) = s
      fieldName (UN (Field s)) = s
      fieldName _ = "_impossible"

      -- this allows the dotted syntax .field
      -- but also the arrowed syntax ->field for compatibility with Idris 1
      recFieldCompat : Rule Name
      recFieldCompat = decorate fname Function postfixProj
                  <|> (decoratedSymbol fname "->"
                       *> decorate fname Function name)

  rewrite_ : OriginDesc -> IndentInfo -> Rule PTerm
  rewrite_ fname indents
      = do b <- bounds (do decoratedKeyword fname "rewrite"
                           rule <- expr pdef fname indents
                           commitKeyword fname indents "in"
                           tm <- typeExpr pdef fname indents
                           pure (rule, tm))
           (rule, tm) <- pure b.val
           pure (PRewrite (boundToFC fname b) rule tm)

  doBlock : OriginDesc -> IndentInfo -> Rule PTerm
  doBlock fname indents
      = do b <- bounds $ decoratedKeyword fname "do" *> block (doAct fname)
           commit
           pure (PDoBlock (virtualiseFC $ boundToFC fname b) Nothing (concat b.val))
    <|> do nsdo <- bounds namespacedIdent
           -- TODO: need to attach metadata correctly here
           the (EmptyRule PTerm) $ case nsdo.val of
                (ns, "do") =>
                   do commit
                      actions <- Core.bounds (block (doAct fname))
                      let fc = virtualiseFC $
                               boundToFC fname (mergeBounds nsdo actions)
                      pure (PDoBlock fc ns (concat actions.val))
                _ => fail "Not a namespaced 'do'"

  validPatternVar : Name -> EmptyRule ()
  validPatternVar (UN Underscore) = pure ()
  validPatternVar (UN (Basic n))
      = unless (lowerFirst n) $
          fail "Not a pattern variable"
  validPatternVar _ = fail "Not a pattern variable"

  doAct : OriginDesc -> IndentInfo -> Rule (List PDo)
  doAct fname indents
      = do b <- bounds (do rig <- multiplicity fname
                           n <- bounds (name <|> UN Underscore <$ symbol "_")
                           -- If the name doesn't begin with a lower case letter, we should
                           -- treat this as a pattern, so fail
                           validPatternVar n.val
                           ty <- optional (decoratedSymbol fname ":" *> typeExpr (pnoeq pdef) fname indents)
                           decoratedSymbol fname "<-"
                           val <- expr pdef fname indents
                           pure (n, rig, ty, val))
           atEnd indents
           let (n, rig, ty, val) = b.val
           pure [DoBind (boundToFC fname b) (boundToFC fname n) n.val rig ty val]
    <|> do decoratedKeyword fname "let"
           commit
           res <- nonEmptyBlock (letBlock fname)
           do b <- bounds (decoratedKeyword fname "in")
              fatalLoc {c = True} b.bounds "Let-in not supported in do block. Did you mean (let ... in ...)?"
             <|>
           do atEnd indents
              pure (mkDoLets fname res)
    <|> do b <- bounds (decoratedKeyword fname "rewrite" *> expr pdef fname indents)
           atEnd indents
           pure [DoRewrite (boundToFC fname b) b.val]
    <|> do e <- bounds (expr plhs fname indents)
           (atEnd indents $> [DoExp (virtualiseFC $ boundToFC fname e) e.val])
             <|> (do ty <- optional (decoratedSymbol fname ":" *> typeExpr (pnoeq pdef) fname indents)
                     b <- bounds $ decoratedSymbol fname "<-" *> [| (expr pnowith fname indents, block (patAlt fname)) |]
                     atEnd indents
                     let (v, alts) = b.val
                     let fc = virtualiseFC $ boundToFC fname (mergeBounds e b)
                     pure [DoBindPat fc e.val ty v alts])

  patAlt : OriginDesc -> IndentInfo -> Rule PClause
  patAlt fname indents
      = do decoratedSymbol fname "|"
           caseAlt fname indents

  lazy : OriginDesc -> IndentInfo -> Rule PTerm
  lazy fname indents
      = do tm <- bounds (decorate fname Typ (exactIdent "Lazy")
                         *> simpleExpr fname indents
                         <* mustFailBecause "Lazy only takes one argument" (continue indents >> simpleExpr fname indents))
           pure (PDelayed (boundToFC fname tm) LLazy tm.val)
    <|> do tm <- bounds (decorate fname Typ (exactIdent "Inf")
                         *> simpleExpr fname indents
                         <* mustFailBecause "Inf only takes one argument" (continue indents >> simpleExpr fname indents))
           pure (PDelayed (boundToFC fname tm) LInf tm.val)
    <|> do tm <- bounds (decorate fname Data (exactIdent "Delay")
                         *> simpleExpr fname indents
                         <* mustFailBecause "Delay only takes one argument" (continue indents >> simpleExpr fname indents))
           pure (PDelay (boundToFC fname tm) tm.val)
    <|> do tm <- bounds (decorate fname Data (exactIdent "Force")
                         *> simpleExpr fname indents
                         <* mustFailBecause "Force only takes one argument" (continue indents >> simpleExpr fname indents))
           pure (PForce (boundToFC fname tm) tm.val)

  binder : OriginDesc -> IndentInfo -> Rule PTerm
  binder fname indents
      = autoImplicitPi fname indents
    <|> defaultImplicitPi fname indents
    <|> forall_ fname indents
    <|> implicitPi fname indents
    <|> autobindOp pdef fname indents
    <|> explicitPi fname indents
    <|> lam fname indents

  typeExpr : ParseOpts -> OriginDesc -> IndentInfo -> Rule PTerm
  typeExpr q fname indents
      = binder fname indents
    <|> ((bounds $ do
            arg <- expr q fname indents
            mscope <- optional $ do
                continue indents
                bd <- bindSymbol fname
                scope <- mustWork $ typeExpr q fname indents
                pure (bd, scope)
            pure (arg, mscope))
        <&> \arg_mscope =>
            let fc = boundToFC fname arg_mscope
                (arg, mscope) = arg_mscope.val
             in mkPi fc arg mscope)

    where
      mkPi : FC -> PTerm -> Maybe (PiInfo PTerm, PTerm) -> PTerm
      mkPi _ arg Nothing = arg
      mkPi fc arg (Just (exp, a))
        = PPi fc top exp Nothing arg a

  export
  expr : ParseOpts -> OriginDesc -> IndentInfo -> Rule PTerm
  expr q fname indents
       = let_ fname indents
     <|> rewrite_ fname indents
     <|> do b <- bounds $
                   do decoratedPragma fname "runElab"
                      expr pdef fname indents
            pure (PRunElab (boundToFC fname b) b.val)
     <|> opExpr q fname indents

  interpBlock : ParseOpts -> OriginDesc -> IndentInfo -> Rule PTerm
  interpBlock q fname idents = interpBegin *> (mustWork $ expr q fname idents) <* interpEnd

  export
  singlelineStr : ParseOpts -> OriginDesc -> IndentInfo -> Rule PTerm
  singlelineStr q fname idents
      = decorate fname Data $
        do b <- bounds $ do begin <- bounds strBegin
                            commit
                            xs <- many $ bounds $ (interpBlock q fname idents) <||> strLitLines
                            pstrs <- case traverse toPStr xs of
                                          Left err => fatalLoc begin.bounds err
                                          Right pstrs => pure $ pstrs
                            strEnd
                            pure (begin.val, pstrs)
           pure $ let (hashtag, str) = b.val in
                      PString (boundToFC fname b) hashtag str
    where
      toPStr : (WithBounds $ Either PTerm (List1 String)) -> Either String PStr
      toPStr x = case x.val of
                      Right (str:::[]) => Right $ StrLiteral (boundToFC fname x) str
                      Right (_:::strs) => Left "Multi-line string is expected to begin with \"\"\""
                      Left tm => Right $ StrInterp (boundToFC fname x) tm

  export
  multilineStr : ParseOpts -> OriginDesc -> IndentInfo -> Rule PTerm
  multilineStr q fname idents
      = decorate fname Data $
        do b <- bounds $ do hashtag <- multilineBegin
                            commit
                            xs <- many $ bounds $ (interpBlock q fname idents) <||> strLitLines
                            endloc <- location
                            strEnd
                            pure (hashtag, endloc, toLines xs [<] [<])
           pure $ let (hashtag, (_, col), xs) = b.val in
                      PMultiline (boundToFC fname b) hashtag (fromInteger $ cast col) xs
    where
      toLines : List (WithBounds $ Either PTerm (List1 String)) ->
                SnocList PStr -> SnocList (List PStr) -> List (List PStr)
      toLines [] line acc = acc <>> [line <>> []]
      toLines (x::xs) line acc = case x.val of
        Left tm =>
          toLines xs (line :< StrInterp (boundToFC fname x) tm) acc
        Right (str:::[]) =>
          toLines xs (line :< StrLiteral (boundToFC fname x) str) acc
        Right (str:::strs@(_::_)) =>
          let fc = boundToFC fname x in
          toLines xs [< StrLiteral fc (last strs)]
            $ acc :< (line <>> [StrLiteral fc str])
            <>< map (\str => [StrLiteral fc str]) (init strs)

  fnDirectOpt : OriginDesc -> Rule PFnOpt
  fnDirectOpt fname
      = do decoratedPragma fname "hint"
           pure $ IFnOpt (Hint True)
    <|> do decoratedPragma fname "globalhint"
           pure $ IFnOpt (GlobalHint False)
    <|> do decoratedPragma fname "defaulthint"
           pure $ IFnOpt (GlobalHint True)
    <|> do decoratedPragma fname "inline"
           commit
           pure $ IFnOpt Inline
    <|> do decoratedPragma fname "unsafe"
           commit
           pure $ IFnOpt Unsafe
    <|> do decoratedPragma fname "noinline"
           commit
           pure $ IFnOpt NoInline
    <|> do decoratedPragma fname "deprecate"
           commit
           pure $ IFnOpt Deprecate
    <|> do decoratedPragma fname "tcinline"
           commit
           pure $ IFnOpt TCInline
    <|> do decoratedPragma fname "extern"
           pure $ IFnOpt ExternFn
    <|> do decoratedPragma fname "macro"
           pure $ IFnOpt Macro
    <|> do decoratedPragma fname "spec"
           ns <- sepBy (decoratedSymbol fname ",") name
           pure $ IFnOpt (SpecArgs ns)
    <|> do decoratedPragma fname "foreign"
           cs <- block (expr pdef fname)
           pure $ PForeign cs
    <|> do (decoratedPragma fname "export"
            <|> withWarning noMangleWarning
                (decoratedPragma fname "nomangle"))
           cs <- block (expr pdef fname)
           pure $ PForeignExport cs
    where
      noMangleWarning : String
      noMangleWarning = """
      DEPRECATED: "%nomangle".
        Use "%export" instead
      """


visOption : OriginDesc ->  Rule Visibility
visOption fname
    = (decoratedKeyword fname "public" *> decoratedKeyword fname "export" $> Public)
    -- If "public export" failed then we try to parse just "public" and emit an error message saying
    -- the user should use "public export"
  <|> (bounds (decoratedKeyword fname "public") >>= \x : WithBounds ()
    => the (Rule Visibility) (fatalLoc x.bounds
           #""public" keyword by itself is not an export modifier, did you mean "public export"?"#))
  <|> (decoratedKeyword fname "export" $> Export)
  <|> (decoratedKeyword fname "private" $> Private)


visibility : OriginDesc -> EmptyRule (WithDefault Visibility Private)
visibility fname
    = (specified <$> visOption fname)
  <|> pure defaulted

exportVisibility : OriginDesc -> EmptyRule (WithDefault Visibility Export)
exportVisibility fname
    = (specified <$> visOption fname)
  <|> pure defaulted

||| A binder with only one name and one type
||| BNF:
||| plainBinder := name ':' typeExpr
plainBinder : (fname : OriginDesc) => (indents : IndentInfo) => Rule PlainBinder
plainBinder = do name <- fcBounds (decoratedSimpleBinderUName fname)
                 decoratedSymbol fname ":"
                 ty <- typeExpr pdef fname indents
                 pure $ MkWithName name ty

||| A binder with multiple names and one type
||| BNF:
||| basicMultiBinder := name (, name)* ':' typeExpr
basicMultiBinder : (fname : OriginDesc) => (indents : IndentInfo) => Rule BasicMultiBinder
basicMultiBinder
  = do rig <- multiplicity fname
       names <- sepBy1 (decoratedSymbol fname ",")
                     $ fcBounds (decoratedSimpleBinderUName fname)
       decoratedSymbol fname ":"
       ty <- typeExpr pdef fname indents
       pure $ MkBasicMultiBinder rig names ty

tyDecls : Rule Name -> String -> OriginDesc -> IndentInfo -> Rule PTypeDecl
tyDecls declName predoc fname indents
    = do bs <- bounds $ do
                  docns <- sepBy1 (decoratedSymbol fname ",")
                                  [| (optDocumentation fname, fcBounds declName) |]
                  b <- bounds $ decoratedSymbol fname ":"
                  mustWorkBecause b.bounds "Expected a type declaration" $ do
                    ty <- the (Rule PTerm) (typeExpr pdef fname indents)
                    pure $ MkPTy docns predoc ty
         atEnd indents
         pure $ bs.withFC

withFlags : OriginDesc -> EmptyRule (List WithFlag)
withFlags fname
    = (do decoratedPragma fname "syntactic"
          (Syntactic ::) <$> withFlags fname)
  <|> pure []


withProblem : OriginDesc -> Int -> IndentInfo -> Rule PWithProblem
withProblem fname col indents
  = do rig <- multiplicity fname
       start <- mustWork $ bounds (decoratedSymbol fname "(")
       wval <- bracketedExpr fname start indents
       prf <- optional $ do
                decoratedKeyword fname "proof"
                pure (!(multiplicity fname), !(decoratedSimpleBinderUName fname))
       pure (MkPWithProblem rig wval prf)

mutual
  parseRHS : (withArgs : Nat) ->
             OriginDesc -> WithBounds t -> Int ->
             IndentInfo -> (lhs : (PTerm, List (FC, PTerm))) -> Rule PClause
  parseRHS withArgs fname start col indents lhs
       = do b <- bounds $ do
                   decoratedSymbol fname "="
                   mustWork $ do
                     continue indents
                     rhs <- typeExpr pdef fname indents
                     ws <- option [] $ whereBlock fname col
                     pure (rhs, ws)
            b' <- bounds peek
            mustWorkBecause b'.bounds "Not the end of a block entry, check indentation" $ atEnd indents
            (rhs, ws) <- pure b.val
            let fc = boundToFC fname (mergeBounds start b)
            pure (MkPatClause fc (uncurry applyWithArgs lhs) rhs ws)
     <|> do b <- bounds $ do
                   decoratedKeyword fname "with"
                   commit
                   flags <- withFlags fname
                   wps <- sepBy1 (decoratedSymbol fname "|") (withProblem fname col indents)
                   ws <- mustWork $ nonEmptyBlockAfter col
                                  $ clause (S (length wps.tail) + withArgs) (Just lhs) fname
                   pure (flags, wps, forget ws)
            (flags, wps, ws) <- pure b.val
            let fc = boundToFC fname (mergeBounds start b)
            pure (MkWithClause fc (uncurry applyWithArgs lhs) wps flags ws)
     <|> do end <- bounds (decoratedKeyword fname "impossible")
            atEnd indents
            pure $ let fc = boundToFC fname (mergeBounds start end) in
                   MkImpossible fc (uncurry applyWithArgs lhs)

  clause : (withArgs : Nat) ->
           IMaybe (isSucc withArgs) (PTerm, List (FC, PTerm)) ->
           OriginDesc -> IndentInfo -> Rule PClause
  clause withArgs mlhs fname indents
      = do b <- bounds (do col   <- column
                           lhsws <- clauseLHS fname indents mlhs
                           extra <- many parseWithArg
                           pure (col, mapSnd (++ extra) lhsws))
           let col = Builtin.fst b.val
           let lhs = Builtin.snd b.val
           let extra = Builtin.snd lhs
           -- Can't have the dependent 'if' here since we won't be able
           -- to infer the termination status of the rule
           ifThenElse (withArgs /= length extra)
              (fatalError $ "Wrong number of 'with' arguments:"
                         ++ " expected " ++ show withArgs
                         ++ " but got " ++ show (length extra))
              (parseRHS withArgs fname b col indents lhs)
    where

      clauseLHS : OriginDesc -> IndentInfo ->
                  IMaybe b (PTerm, List (FC, PTerm)) ->
                  Rule (PTerm, List (FC, PTerm))
      -- we aren't in a `with` so there is nothing to skip
      clauseLHS fname indent Nothing
        = (,[]) <$> opExpr plhs fname indents
      -- in a with clause, give a different meaning to a `_` lhs
      clauseLHS fname indent (Just lhs)
        = do e <- opExpr plhs fname indents
             pure $ case e of
               PImplicit fc =>
                 let vfc = virtualiseFC fc in
                 bimap (substFC vfc) (map (map $ substFC vfc)) lhs
               _ => (e, [])

      parseWithArg : Rule (FC, PTerm)
      parseWithArg
          = do decoratedSymbol fname "|"
               tm <- bounds (expr plhs fname indents)
               pure (boundToFC fname tm, tm.val)

mkTyConType : OriginDesc -> FC -> List (WithBounds Name) -> PTerm
mkTyConType fname fc [] = PType (virtualiseFC fc)
mkTyConType fname fc (x :: xs)
   = let bfc = boundToFC fname x in
     PPi bfc top Explicit Nothing (PType (virtualiseFC fc))
     $ mkTyConType fname fc xs

mkDataConType : PTerm -> List (WithFC ArgType) -> Maybe PTerm
mkDataConType ret [] = Just ret
mkDataConType ret (MkFCVal fc (UnnamedExpArg x) :: xs)
    = PPi fc top Explicit Nothing x <$> mkDataConType ret xs
mkDataConType ret (MkFCVal fc (UnnamedAutoArg x) :: xs)
    = PPi fc top AutoImplicit Nothing x <$> mkDataConType ret xs
mkDataConType _ _ -- with and named applications not allowed in simple ADTs
    = Nothing

simpleCon : OriginDesc -> PTerm -> IndentInfo -> Rule PTypeDecl
simpleCon fname ret indents
    = do b <- bounds (do cdoc   <- optDocumentation fname
                         cname  <- fcBounds $ decoratedDataConstructorName fname
                         params <- the (EmptyRule $ List $ WithFC $ List ArgType)
                                     $ many (fcBounds $ argExpr plhs fname indents)
                         let conType = the (Maybe PTerm) (mkDataConType ret
                                                            (concat (map distribFC params)))
                         fromMaybe (fatalError "Named arguments not allowed in ADT constructors")
                                   (pure . MkPTy (singleton ("", cname)) cdoc <$> conType)
                         )
         atEnd indents
         pure b.withFC

simpleData : OriginDesc -> WithBounds t ->
             WithBounds Name -> IndentInfo -> Rule PDataDecl
simpleData fname start tyName indents
    = do b <- bounds (do params <- many (bounds $ decorate fname Bound name)
                         tyend <- bounds (decoratedSymbol fname "=")
                         mustWork $ do
                           let tyfc = boundToFC fname (mergeBounds start tyend)
                           let tyCon = PRef (boundToFC fname tyName) tyName.val
                           let toPRef = \ t => PRef (boundToFC fname t) t.val
                           let conRetTy = papply tyfc tyCon (map toPRef params)
                           cons <- sepBy1 (decoratedSymbol fname "|") (simpleCon fname conRetTy indents)
                           pure (params, tyfc, forget cons))
         (params, tyfc, cons) <- pure b.val
         pure (MkPData (boundToFC fname (mergeBounds start b)) tyName.val
                       (Just (mkTyConType fname tyfc params)) [] cons)

dataOpt : OriginDesc -> Rule DataOpt
dataOpt fname
    = (decorate fname Keyword (exactIdent "noHints") $> NoHints)
  <|> (decorate fname Keyword (exactIdent "uniqueSearch") $> UniqueSearch)
  <|> (do b   <- bounds $ decorate fname Keyword (exactIdent "search")
          det <- mustWorkBecause b.bounds "Expected list of determining parameters" $
                   some (decorate fname Bound name)
          pure $ SearchBy det)
  <|> (decorate fname Keyword (exactIdent "external") $> External)
  <|> (decorate fname Keyword (exactIdent "noNewtype") $> NoNewtype)

dataOpts : OriginDesc -> EmptyRule (List DataOpt)
dataOpts fname = option [] $ do
  decoratedSymbol fname "["
  opts <- sepBy1 (decoratedSymbol fname ",") (dataOpt fname)
  decoratedSymbol fname "]"
  pure (forget opts)

dataBody : OriginDesc -> Int -> WithBounds t -> Name -> IndentInfo -> Maybe PTerm ->
          EmptyRule PDataDecl
dataBody fname mincol start n indents ty
    = do ty <- maybe (fail "Telescope is not optional in forward declaration") pure ty
         atEndIndent indents
         pure (MkPLater (boundToFC fname start) n ty)
  <|> do b <- bounds (do (mustWork $ decoratedKeyword fname "where")
                         opts <- dataOpts fname
                         cs <- blockAfter mincol (tyDecls (mustWork $ decoratedDataConstructorName fname) "" fname)
                         pure (opts, cs))
         (opts, cs) <- pure b.val
         pure (MkPData (boundToFC fname (mergeBounds start b)) n ty opts cs)

gadtData : OriginDesc -> Int -> WithBounds t ->
           WithBounds Name -> IndentInfo -> EmptyRule PDataDecl
gadtData fname mincol start tyName indents
    = do ty <- optional $
                 do decoratedSymbol fname ":"
                    commit
                    typeExpr pdef fname indents
         dataBody fname mincol start tyName.val indents ty

dataDeclBody : OriginDesc -> IndentInfo -> Rule PDataDecl
dataDeclBody fname indents
    = do b <- bounds (do col <- column
                         decoratedKeyword fname "data"
                         n <- mustWork (bounds $ decoratedDataTypeName fname)
                         pure (col, n))
         (col, n) <- pure b.val
         simpleData fname b n indents <|> gadtData fname col b n indents

-- a data declaration can have a visibility and an optional totality (#1404)
dataVisOpt : OriginDesc -> EmptyRule (WithDefault Visibility Private, Maybe TotalReq)
dataVisOpt fname
    = do { vis <- visOption   fname ; mbtot <- optional (totalityOpt fname) ; pure (specified vis, mbtot) }
  <|> do { tot <- totalityOpt fname ; vis <- visibility fname ; pure (vis, Just tot) }
  <|> pure (defaulted, Nothing)

dataDecl : (fname : OriginDesc) => (indents : IndentInfo) => Rule PDeclNoFC
dataDecl
    = do doc         <- optDocumentation fname
         (vis,mbTot) <- dataVisOpt fname
         dat         <- dataDeclBody fname indents
         pure (PData doc vis mbTot dat)

stripBraces : String -> String
stripBraces str = pack (drop '{' (reverse (drop '}' (reverse (unpack str)))))
  where
    drop : Char -> List Char -> List Char
    drop c [] = []
    drop c (c' :: xs) = if c == c' then drop c xs else c' :: xs

onoff : Rule Bool
onoff
   = (exactIdent "on" $> True)
 <|> (exactIdent "off" $> False)
 <|> fail "expected 'on' or 'off'"

extension : Rule LangExt
extension
    = (exactIdent "ElabReflection" $> ElabReflection)
  <|> (exactIdent "Borrowing" $> Borrowing)
  <|> fail "expected either 'ElabReflection' or 'Borrowing'"

logLevel : OriginDesc -> Rule (Maybe LogLevel)
logLevel fname
  = (Nothing <$ decorate fname Keyword (exactIdent "off"))
    <|> do topic <- optional (split ('.' ==) <$> simpleStr)
           lvl <- intLit
           pure (Just (mkLogLevel' topic (fromInteger lvl)))
    <|> fail "expected a log level"

directive : (fname : OriginDesc) => (indents : IndentInfo) => Rule Directive
directive
    = do decoratedPragma fname "hide"
         n <- (fixityNS <|> (HideName <$> name))
         atEnd indents
         pure (Hide n)
  <|> do decoratedPragma fname "unhide"
         n <- name
         atEnd indents
         pure (Unhide n)
  <|> do decoratedPragma fname "foreign_impl"
         n <- name
         cs <- block (expr pdef fname)
         atEnd indents
         pure (ForeignImpl n cs)
--   <|> do pragma "hide_export"
--          n <- name
--          atEnd indents
--          pure (Hide True n)
  <|> do decoratedPragma fname "logging"
         lvl <- logLevel fname
         atEnd indents
         pure (Logging lvl)
  <|> do decoratedPragma fname "auto_lazy"
         b <- onoff
         atEnd indents
         pure (LazyOn b)
  <|> do decoratedPragma fname "unbound_implicits"
         b <- onoff
         atEnd indents
         pure (UnboundImplicits b)
  <|> do decoratedPragma fname "prefix_record_projections"
         b <- onoff
         atEnd indents
         pure (PrefixRecordProjections b)
  <|> do decoratedPragma fname "totality_depth"
         lvl <- decorate fname Keyword $ intLit
         atEnd indents
         pure (TotalityDepth (fromInteger lvl))
  <|> do decoratedPragma fname "ambiguity_depth"
         lvl <- decorate fname Keyword $ intLit
         atEnd indents
         pure (AmbigDepth (fromInteger lvl))
  <|> do decoratedPragma fname "auto_implicit_depth"
         dpt <- decorate fname Keyword $ intLit
         atEnd indents
         pure (AutoImplicitDepth (fromInteger dpt))
  <|> do decoratedPragma fname "nf_metavar_threshold"
         dpt <- decorate fname Keyword $ intLit
         atEnd indents
         pure (NFMetavarThreshold (fromInteger dpt))
  <|> do decoratedPragma fname "search_timeout"
         t <- decorate fname Keyword $ intLit
         atEnd indents
         pure (SearchTimeout t)
  <|> do decoratedPragma fname "pair"
         ty <- name
         f <- name
         s <- name
         atEnd indents
         pure (PairNames ty f s)
  <|> do decoratedPragma fname "rewrite"
         eq <- name
         rw <- name
         atEnd indents
         pure (RewriteName eq rw)
  <|> do decoratedPragma fname "integerLit"
         n <- name
         atEnd indents
         pure (PrimInteger n)
  <|> do decoratedPragma fname "stringLit"
         n <- name
         atEnd indents
         pure (PrimString n)
  <|> do decoratedPragma fname "charLit"
         n <- name
         atEnd indents
         pure (PrimChar n)
  <|> do decoratedPragma fname "doubleLit"
         n <- name
         atEnd indents
         pure (PrimDouble n)
  <|> do decoratedPragma fname "TTImpLit"
         n <- name
         atEnd indents
         pure (PrimTTImp n)
  <|> do decoratedPragma fname "nameLit"
         n <- name
         atEnd indents
         pure (PrimName n)
  <|> do decoratedPragma fname "declsLit"
         n <- name
         atEnd indents
         pure (PrimDecls n)
  <|> do decoratedPragma fname "name"
         n <- name
         ns <- sepBy1 (decoratedSymbol fname ",")
                      (decoratedSimpleBinderUName fname)
         atEnd indents
         pure (Names n (forget (map nameRoot ns)))
  <|> do decoratedPragma fname "start"
         e <- expr pdef fname indents
         atEnd indents
         pure (StartExpr e)
  <|> do decoratedPragma fname "allow_overloads"
         n <- name
         atEnd indents
         pure (Overloadable n)
  <|> do decoratedPragma fname "language"
         e <- mustWork extension
         atEnd indents
         pure (Extension e)
  <|> do decoratedPragma fname "default"
         tot <- totalityOpt fname
         atEnd indents
         pure (DefaultTotality tot)

fix : Rule Fixity
fix
    = (keyword "infixl" $> InfixL)
  <|> (keyword "infixr" $> InfixR)
  <|> (keyword "infix"  $> Infix)
  <|> (keyword "prefix" $> Prefix)

namespaceHead : OriginDesc -> Rule Namespace
namespaceHead fname
  = do decoratedKeyword fname "namespace"
       decorate fname Namespace $ mustWork namespaceId

parameters {auto fname : OriginDesc} {auto indents : IndentInfo}
  namespaceDecl : Rule PDeclNoFC
  namespaceDecl
      = do doc   <- optDocumentation fname -- documentation is not recoded???
           col   <- column
           ns    <- namespaceHead fname
           ds    <- blockAfter col (topDecl fname)
           pure (PNamespace  ns (collectDefs ds))

  transformDecl : Rule PDeclNoFC
  transformDecl
      = do decoratedPragma fname "transform"
           n <- simpleStr
           lhs <- expr plhs fname indents
           decoratedSymbol fname "="
           rhs <- expr pnowith fname indents
           pure (PTransform n lhs rhs)

  runElabDecl : Rule PDeclNoFC
  runElabDecl
      = do
           decoratedPragma fname "runElab"
           tm <- expr pnowith fname indents
           pure (PRunElabDecl tm)

  ||| failDecls := 'failing' simpleStr? nonEmptyBlock
  failDecls : Rule PDeclNoFC
  failDecls
      = do
           col <- column
           decoratedKeyword fname "failing"
           commit
           msg <- optional (decorate fname Data simpleStr)
           ds <- nonEmptyBlockAfter col (topDecl fname)
           pure $ PFail msg (collectDefs $ forget ds)

  ||| mutualDecls := 'mutual' nonEmptyBlock
  mutualDecls : Rule PDeclNoFC
  mutualDecls
      = do
           col <- column
           decoratedKeyword fname "mutual"
           commit
           ds <- nonEmptyBlockAfter col (topDecl fname)
           pure (PMutual (forget ds))

  usingDecls : Rule PDeclNoFC
  usingDecls
      = do col <- column
           decoratedKeyword fname "using"
           commit
           decoratedSymbol fname "("
           us <- sepBy (decoratedSymbol fname ",")
                       (do n <- optional $ do
                                      x <- unqualifiedName
                                      decoratedSymbol fname ":"
                                      pure (UN $ Basic x)
                           ty <- typeExpr pdef fname indents
                           pure (n, ty))
           decoratedSymbol fname ")"
           ds <- nonEmptyBlockAfter col (topDecl fname)
           pure (PUsing us (collectDefs (forget ds)))

  ||| builtinDecl := 'builtin' builtinType name
  builtinDecl : Rule PDeclNoFC
  builtinDecl
      = do decoratedPragma fname "builtin"
           commit
           t <- builtinType
           n <- name
           pure $ PBuiltin t n

visOpt : OriginDesc -> Rule (Either Visibility PFnOpt)
visOpt fname
    = do vis <- visOption fname
         pure (Left vis)
  <|> do tot <- fnOpt fname
         pure (Right tot)
  <|> do opt <- fnDirectOpt fname
         pure (Right opt)

getVisibility : Maybe Visibility -> List (Either Visibility PFnOpt) ->
                EmptyRule Visibility
getVisibility Nothing [] = pure Private
getVisibility (Just vis) [] = pure vis
getVisibility Nothing (Left x :: xs) = getVisibility (Just x) xs
getVisibility (Just vis) (Left x :: xs)
   = fatalError "Multiple visibility modifiers"
getVisibility v (_ :: xs) = getVisibility v xs

recordConstructor : OriginDesc -> Rule (String, Name)
recordConstructor fname
  = do doc <- optDocumentation fname
       decorate fname Keyword $ exactIdent "constructor"
       n <- mustWork $ decoratedDataConstructorName fname
       pure (doc, n)

autoImplicitField : OriginDesc -> IndentInfo -> Rule (PiInfo t)
autoImplicitField fname _ = AutoImplicit <$ decoratedKeyword fname "auto"

defImplicitField : OriginDesc -> IndentInfo -> Rule (PiInfo PTerm)
defImplicitField fname indents = do
  decoratedKeyword fname "default"
  commit
  t <- simpleExpr fname indents
  pure (DefImplicit t)

constraints : OriginDesc -> IndentInfo -> EmptyRule (List (Maybe Name, PTerm))
constraints fname indents
    = do tm <- appExpr pdef fname indents
         decoratedSymbol fname "=>"
         more <- constraints fname indents
         pure ((Nothing, tm) :: more)
  <|> do decoratedSymbol fname "("
         n <- decorate fname Bound name
         decoratedSymbol fname ":"
         tm <- typeExpr pdef fname indents
         decoratedSymbol fname ")"
         decoratedSymbol fname "=>"
         more <- constraints fname indents
         pure ((Just n, tm) :: more)
  <|> pure []

implBinds : OriginDesc -> IndentInfo -> (namedImpl : Bool) -> EmptyRule (List (FC, RigCount, Name, PiInfo PTerm, PTerm))
implBinds fname indents namedImpl = concatMap (map adjust) <$> go where

  adjust : (RigCount, WithFC Name, a) -> (FC, RigCount, Name, a)
  adjust (r, wn, ty) = (virtualiseFC wn.fc, r, wn.val, ty)

  isDefaultImplicit : PiInfo a -> Bool
  isDefaultImplicit (DefImplicit _) = True
  isDefaultImplicit _               = False

  go : EmptyRule (List (List (RigCount, WithFC Name, PiInfo PTerm, PTerm)))
  go = do decoratedSymbol fname "{"
          piInfo <- bounds $ option Implicit $ defImplicitField fname indents
          when (not namedImpl && isDefaultImplicit piInfo.val) $
            fatalLoc piInfo.bounds "Default implicits are allowed only for named implementations"
          ns <- map
                    (\case (MkBasicMultiBinder rig names type) => map (\nm => (rig, nm, piInfo.val, type)) (forget names))
                    (pibindListName fname indents)
          let ns = the (List (ZeroOneOmega, (WithFC Name, (PiInfo (PTerm' Name), PTerm' Name)))) ns
          commitSymbol fname "}"
          commitSymbol fname "->"
          more <- go
          pure (ns :: more)
    <|> pure []

fieldDecl : (fname : OriginDesc) => IndentInfo -> Rule PField
fieldDecl indents
      = do doc <- optDocumentation fname
           decoratedSymbol fname "{"
           commit
           impl <- option Implicit (autoImplicitField fname indents <|> defImplicitField fname indents)
           fs <- fieldBody doc impl
           decoratedSymbol fname "}"
           atEnd indents
           pure fs
    <|> do doc <- optDocumentation fname
           fs <- fieldBody doc Explicit
           atEnd indents
           pure fs
  where
    fieldBody : String -> PiInfo PTerm -> Rule (PField)
    fieldBody doc p
        = do b <- bounds (do
                    rig <- multiplicity fname
                    ns <- sepBy1 (decoratedSymbol fname ",")
                            (decorate fname Function name
                               <|> (do b <- bounds (symbol "_")
                                       fatalLoc {c = True} b.bounds "Fields have to be named"))
                    decoratedSymbol fname ":"
                    ty <- typeExpr pdef fname indents
                    pure (MkRecordField doc rig p (forget ns) ty))
             pure b.withFC

parameters {auto fname : OriginDesc} {auto indents : IndentInfo}

  ifaceParam : Rule BasicMultiBinder
  ifaceParam
      = parens fname basicMultiBinder
    <|> do n <- fcBounds (decorate fname Bound name)
           pure (MkBasicMultiBinder erased (singleton n) (PInfer n.fc))

  ifaceDecl : Rule PDeclNoFC
  ifaceDecl
      = do  doc   <- optDocumentation fname
            vis   <- visibility fname
            col   <- column
            decoratedKeyword fname "interface"
            commit
            cons   <- constraints fname indents
            n      <- decorate fname Typ name
            params <- many ifaceParam
            det    <- optional $ do
              b <- bounds $ decoratedSymbol fname "|"
              mustWorkBecause b.bounds "Expected list of determining parameters" $
                sepBy1 (decoratedSymbol fname ",") (decorate fname Bound name)
            decoratedKeyword fname "where"
            dc <- optional (recordConstructor fname)
            body <- blockAfter col (topDecl fname)
            pure (PInterface
                         vis cons n doc params det dc (collectDefs body))

  implDecl : Rule PDeclNoFC
  implDecl
      = do doc     <- optDocumentation fname
           visOpts <- many (visOpt fname)
           vis     <- getVisibility Nothing visOpts
           let opts = mapMaybe getRight visOpts
           col <- column
           option () (decoratedKeyword fname "implementation")
           iname  <- optional $ decoratedSymbol fname "["
                             *> decorate fname Function name
                             <* decoratedSymbol fname "]"
           impls  <- implBinds fname indents (isJust iname)
           cons   <- constraints fname indents
           n      <- decorate fname Typ name
           params <- many (continue indents *> simpleExpr fname indents)
           nusing <- option [] $ decoratedKeyword fname "using"
                              *> forget <$> some (decorate fname Function name)
           body <- optional $ decoratedKeyword fname "where" *> blockAfter col (topDecl fname)
           atEnd indents
           pure $
              PImplementation vis opts Single impls cons n params iname nusing
                               (map collectDefs body)

  localClaim : Rule PClaimData
  localClaim
      = do doc     <- optDocumentation fname
           visOpts <- many (visOpt fname)
           vis     <- getVisibility Nothing visOpts
           let opts = mapMaybe getRight visOpts
           rig  <- multiplicity fname
           cls  <- tyDecls (decorate fname Function name)
                           doc fname indents
           pure $ MkPClaim rig vis opts cls


  -- A Single binder with multiple names
  typedArg : Rule PBinder
  typedArg
      = do params <- parens fname $ pibindListName fname indents
           pure $ MkPBinder Explicit params
    <|> do decoratedSymbol fname "{"
           commit
           info <-
                    (pure  AutoImplicit <* decoratedKeyword fname "auto"
                <|> (decoratedKeyword fname "default" *> DefImplicit <$> simpleExpr fname indents)
                <|> pure      Implicit)
           params <- pibindListName fname indents
           decoratedSymbol fname "}"
           pure $ MkPBinder info params

  ||| Record parameter, can be either a typed binder or a name
  ||| BNF:
  ||| recordParam := typedArg | name
  recordParam : Rule PBinder
  recordParam
      = typedArg
    <|> do n <- fcBounds (decoratedSimpleBinderUName fname)
           pure (MkFullBinder Explicit top n $ PInfer n.fc)

  -- A record without a where is a forward declaration
  recordBody : String -> WithDefault Visibility Private ->
               Maybe TotalReq ->
               Int ->
               Name ->
               List PBinder ->
               EmptyRule PDeclNoFC
  recordBody doc vis mbtot col n params
      = do atEndIndent indents
           pure (PRecord doc vis mbtot (MkPRecordLater n params))
    <|> do mustWork $ decoratedKeyword fname "where"
           opts <- dataOpts fname
           dcflds <- blockWithOptHeaderAfter col
                       (\ idt => recordConstructor fname <* atEnd idt)
                       fieldDecl
           pure (PRecord doc vis mbtot
                  (MkPRecord n params opts (fst dcflds) (snd dcflds)))

  recordDecl : Rule PDeclNoFC
  recordDecl
      = do doc         <- optDocumentation fname
           (vis,mbtot) <- dataVisOpt fname
           col         <- column
           decoratedKeyword fname "record"
           n       <- mustWork (decoratedDataTypeName fname)
           paramss <- many (continue indents >> recordParam)
           recordBody doc vis mbtot col n paramss

  ||| Parameter blocks
  ||| BNF:
  ||| paramDecls := 'parameters' (oldParamDecls | newParamDecls) indentBlockDefs
  paramDecls : Rule PDeclNoFC
  paramDecls = do
           startCol <- column
           b1 <- decoratedKeyword fname "parameters"
           commit
           args <- Right <$> newParamDecls
               <|> Left <$> withWarning "DEPRECATED: old parameter syntax https://github.com/idris-lang/Idris2/issues/3447" oldParamDecls
           commit
           declarations <- nonEmptyBlockAfter startCol (topDecl fname)
           pure (PParameters args
                    (collectDefs (forget declarations)))

    where
      oldParamDecls : Rule (List1 PlainBinder)
      oldParamDecls
          = parens fname $ sepBy1 (decoratedSymbol fname ",") plainBinder

      newParamDecls : Rule (List1 PBinder)
      newParamDecls = some typedArg


  definition : Rule PDeclNoFC
  definition
      = do nd <- clause 0 Nothing fname indents
           pure (PDef (singleton nd))

  operatorBindingKeyword : EmptyRule BindingModifier
  operatorBindingKeyword
    =   (decoratedKeyword fname "autobind" >> pure Autobind)
    <|> (decoratedKeyword fname "typebind" >> pure Typebind)
    <|> pure NotBinding

  fixDecl : Rule PDecl
  fixDecl
      = do vis <- exportVisibility fname
           binding <- operatorBindingKeyword
           b <- fcBounds (do fixity <- decorate fname Keyword $ fix
                             commit
                             prec <- decorate fname Keyword $ intLit
                             ops <- sepBy1 (decoratedSymbol fname ",") iOperator
                             pure (MkPFixityData vis binding fixity (fromInteger prec) ops)
                       )
           pure (mapFC PFixity b)

-- The compiler cannot infer the values for c1 and c2 so I had to write it
-- this way.
-- - Andre
cgDirectiveDecl : Rule PDeclNoFC
cgDirectiveDecl
  = (>>=) {c1 = True, c2 = False} cgDirective $ \dir =>
      let (cg1, cg2) = span isAlphaNum dir
      in the (EmptyRule PDeclNoFC) $ pure $
            PDirective (CGAction cg1 (stripBraces (trim cg2)))

-- Declared at the top
-- topDecl : OriginDesc -> IndentInfo -> Rule (List PDecl)
topDecl fname indents
      -- Specifically check if the user has attempted to use a reserved identifier to begin their declaration to give improved error messages.
      -- i.e. the claim "String : Type" is a parse error, but the underlying reason may not be clear to new users.
    = do id <- anyReservedIdent
         the (Rule PDecl) $ fatalLoc id.bounds "Cannot begin a declaration with a reserved identifier"
  <|> fcBounds dataDecl
  <|> fcBounds (PClaim <$> localClaim)
  <|> fcBounds (PDirective <$> directive)
  <|> fcBounds implDecl
  <|> fcBounds definition
  <|> fixDecl
  <|> fcBounds ifaceDecl
  <|> fcBounds recordDecl
  <|> fcBounds namespaceDecl
  <|> fcBounds failDecls
  <|> fcBounds mutualDecls
  <|> fcBounds paramDecls
  <|> fcBounds usingDecls
  <|> fcBounds builtinDecl
  <|> fcBounds runElabDecl
  <|> fcBounds transformDecl
  <|> fcBounds cgDirectiveDecl
      -- If the user tried to begin a declaration with any other keyword, then show a more informative error.
  <|> do kw <- bounds anyKeyword
         the (Rule PDecl) $ fatalLoc kw.bounds "Keyword '\{kw.val}' is not a valid start to a declaration"
  <|> fatalError "Couldn't parse declaration"

-- All the clauses get parsed as one-clause definitions. Collect any
-- neighbouring clauses into one definition. This might mean merging two
-- functions which are different, if there are forward declarations,
-- but we'll split them in Desugar.idr. We can't do this now, because we
-- haven't resolved operator precedences yet.
-- Declared at the top.
-- collectDefs : List PDecl -> List PDecl
collectDefs [] = []
collectDefs (MkFCVal annot (PDef cs) :: ds)
    = let (csWithFC, rest) = spanBy isPDef ds
          cs' = cs ++ concat (map val csWithFC)
          annot' = foldr
                   (\fc1, fc2 => fromMaybe EmptyFC (mergeFC fc1 fc2))
                   annot
                   (map fc csWithFC)
      in
          MkFCVal annot' (PDef cs') :: assert_total (collectDefs rest)
collectDefs (MkFCVal annot (PNamespace ns nds) :: ds)
    = MkFCVal annot (PNamespace ns (collectDefs nds)) :: collectDefs ds
collectDefs (MkFCVal fc (PMutual nds) :: ds)
    = MkFCVal fc (PMutual (collectDefs nds)) :: collectDefs ds
collectDefs (d :: ds)
    = d :: collectDefs ds

export
import_ : OriginDesc -> IndentInfo -> Rule Import
import_ fname indents
    = do b <- bounds (do decoratedKeyword fname "import"
                         reexp <- option False (decoratedKeyword fname "public" $> True)
                         ns <- decorate fname Module $ mustWork moduleIdent
                         nsAs <- option (miAsNamespace ns)
                                        (do decorate fname Keyword $ exactIdent "as"
                                            decorate fname Namespace $ mustWork namespaceId)
                         pure (reexp, ns, nsAs))
         atEnd indents
         (reexp, ns, nsAs) <- pure b.val
         pure (MkImport (boundToFC fname b) reexp ns nsAs)

export
progHdr : OriginDesc -> EmptyRule Module
progHdr fname
    = do b <- bounds (do doc    <- optDocumentation fname
                         nspace <- option (nsAsModuleIdent mainNS)
                                     (do decoratedKeyword fname "module"
                                         decorate fname Module $ mustWork moduleIdent)
                         imports <- block (import_ fname)
                         pure (doc, nspace, imports))
         (doc, nspace, imports) <- pure b.val
         pure (MkModule (boundToFC fname b)
                        nspace imports doc [])

export
prog : OriginDesc -> EmptyRule Module
prog fname
    = do mod <- progHdr fname
         ds <- block (topDecl fname)
         pure $ { decls := collectDefs ds} mod

parseMode : Rule REPLEval
parseMode
     = do exactIdent "typecheck"
          pure EvalTC
   <|> do exactIdent "tc"
          pure EvalTC
   <|> do exactIdent "normalise"
          pure NormaliseAll
   <|> do exactIdent "default"
          pure NormaliseAll
   <|> do exactIdent "normal"
          pure NormaliseAll
   <|> do exactIdent "normalize" -- oh alright then
          pure NormaliseAll
   <|> do exactIdent "execute"
          pure Execute
   <|> do exactIdent "exec"
          pure Execute
   <|> do exactIdent "scheme"
          pure Scheme

setVarOption : Rule REPLOpt
setVarOption
    = do exactIdent "eval"
         mode <- option NormaliseAll parseMode
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
  <|> do exactIdent "showmachinenames"
         pure (ShowMachineNames set)
  <|> do exactIdent "showtypes"
         pure (ShowTypes set)
  <|> do exactIdent "profile"
         pure (Profile set)
  <|> do exactIdent "evaltiming"
         pure (EvalTiming set)
  <|> if set then setVarOption else fatalError "Unrecognised option"

replCmd : List String -> Rule ()
replCmd [] = fail "Unrecognised command"
replCmd (c :: cs)
    = exactIdent c
  <|> symbol c
  <|> replCmd cs

cmdName : String -> Rule String
cmdName str = do
  _ <- optional (symbol ":")
  terminal ("Unrecognised REPL command '" ++ str ++ "'") $
           \case
              (Ident s)       => if s == str then Just s else Nothing
              (Keyword kw)    => if kw == str then Just kw else Nothing
              (Symbol "?")    => Just "?"
              (Symbol ":?")   => Just "?"   -- `:help :?` is a special case
              _ => Nothing

export
data CmdArg : Type where
     ||| The command takes no arguments.
     NoArg : CmdArg

     ||| The command takes a name.
     NameArg : CmdArg

     ||| The command takes an expression.
     ExprArg : CmdArg

     ||| The command takes a documentation directive.
     DocArg : CmdArg

     ||| The command takes a list of declarations
     DeclsArg : CmdArg

     ||| The command takes a number.
     NumberArg : CmdArg

     ||| The command takes a number or auto.
     AutoNumberArg : CmdArg

     ||| The command takes an option.
     OptionArg : CmdArg

     ||| The command takes a file.
     FileArg : CmdArg

     ||| The command takes a module.
     ModuleArg : CmdArg

     ||| The command takes a string
     StringArg : CmdArg

     ||| The command takes a on or off.
     OnOffArg : CmdArg

     ||| The command takes an argument documenting its name
     NamedCmdArg : String -> CmdArg -> CmdArg

     ||| The command takes an argument documenting its default value
     WithDefaultArg : String -> CmdArg -> CmdArg

     ||| The command takes arguments separated by commas
     CSVArg : CmdArg -> CmdArg

     ||| The command takes multiple arguments.
     Args : List CmdArg -> CmdArg

mutual
  covering
  showCmdArg : CmdArg -> String
  showCmdArg NoArg = ""
  showCmdArg NameArg = "name"
  showCmdArg ExprArg = "expr"
  showCmdArg DocArg = "keyword|expr"
  showCmdArg DeclsArg = "decls"
  showCmdArg NumberArg = "number"
  showCmdArg AutoNumberArg = "number|auto"
  showCmdArg OptionArg = "option"
  showCmdArg FileArg = "file"
  showCmdArg ModuleArg = "module"
  showCmdArg StringArg = "string"
  showCmdArg OnOffArg = "(on|off)"
  showCmdArg (CSVArg arg) = "[" ++ showCmdArg arg ++ "]"
  showCmdArg (WithDefaultArg value arg) = showCmdArg arg ++ "|" ++ value
  showCmdArg (NamedCmdArg name arg) = name ++ ":" ++ showCmdArg arg
  showCmdArg args@(Args _) = show args

  export
  covering
  Show CmdArg where
    show NoArg = ""
    show OnOffArg = "(on|off)"
    show (Args args) = showSep " " (map show args)
    show arg = "<" ++ showCmdArg arg ++ ">"

public export
knownCommands : List (String, String)
knownCommands =
  explain ["t", "type"] "Check the type of an expression" ++
  [ ("ti", "Check the type of an expression, showing implicit arguments")
  , ("printdef", "Show the definition of a pattern-matching function")
  ] ++
  explain ["s", "search"] "Search for values by type" ++
  [ ("di", "Show debugging information for a name")
  ] ++
  explain ["module", "import"] "Import an extra module" ++
  [ ("package", "Import every module of the package")
  ] ++
  explain ["q", "quit", "exit"] "Exit the Idris system" ++
  [ ("cwd", "Displays the current working directory")
  , ("cd", "Change the current working directory")
  , ("sh", "Run a shell command")
  , ("set"
    , unlines   -- FIXME: this should be a multiline string (see #2087)
      [ "Set an option"
      , "  eval                specify what evaluation mode to use:"
      , "                        typecheck|tc"
      , "                        normalise|normalize|normal"
      , "                        execute|exec"
      , "                        scheme"
      , ""
      , "  editor              specify the name of the editor command"
      , ""
      , "  cg                  specify the codegen/backend to use"
      , "                      builtin codegens are:"
      , "                        chez"
      , "                        racket"
      , "                        refc"
      , "                        node"
      , ""
      , "  showimplicits       enable displaying implicit arguments as part of the"
      , "                      output"
      , ""
      , "  shownamespace       enable displaying namespaces as part of the output"
      , ""
      , "  showmachinenames    enable displaying machine names as part of the"
      , "                      output"
      , ""
      , "  showtypes           enable displaying the type of the term as part of"
      , "                      the output"
      , ""
      , "  profile"
      , ""
      , "  evaltiming          enable timing how long evaluation takes and"
      , "                      displaying this before the printing of the output"
      ]
    )
  , ("unset", "Unset an option")
  , ("opts", "Show current options settings")
  ] ++
  explain ["c", "compile"] "Compile to an executable" ++
  [ ("exec", "Compile to an executable and run")
  , ("directive", "Set a codegen-specific directive")
  ] ++
  explain ["l", "load"] "Load a file" ++
  explain ["r", "reload"] "Reload current file" ++
  explain ["e", "edit"] "Edit current file using $EDITOR or $VISUAL" ++
  explain ["miss", "missing"] "Show missing clauses" ++
  [ ("total", "Check the totality of a name")
  , ("doc", "Show documentation for a keyword, a name, or a primitive")
  , ("browse", "Browse contents of a namespace")
  ] ++
  explain ["log", "logging"] "Set logging level" ++
  [ ("consolewidth", "Set the width of the console output (0 for unbounded) (auto by default)")
  ] ++
  explain ["colour", "color"] "Whether to use colour for the console output (enabled by default)" ++
  explain ["m", "metavars"] "Show remaining proof obligations (metavariables or holes)" ++
  [ ("typeat", "Show type of term <n> defined on line <l> and column <c>")
  ] ++
  explain ["cs", "casesplit"] "Case split term <n> defined on line <l> and column <c>" ++
  explain ["ac", "addclause"] "Add clause to term <n> defined on line <l>" ++
  explain ["ml", "makelemma"] "Make lemma for term <n> defined on line <l>" ++
  explain ["mc", "makecase"] "Make case on term <n> defined on line <l>" ++
  explain ["mw", "makewith"] "Add with expression on term <n> defined on line <l>" ++
  [ ("intro", "Introduce unambiguous constructor in hole <n> defined on line <l>")
  , ("refine", "Refine hole <h> with identifier <n> on line <l>")
  ] ++
  explain ["ps", "proofsearch"] "Search for a proof" ++
  [ ("psnext", "Show next proof")
  , ("gd", "Try to generate a definition using proof-search")
  , ("gdnext", "Show next definition")
  , ("version", "Display the Idris version")
  ] ++
  explain ["?", "h", "help"] (unlines     -- FIXME: this should be a multiline string (see #2087)
        [ "Display help text, optionally of a specific command.\n"
        , "If run without arguments, lists all the REPL commands along with their"
        , "initial line of help text.\n"
        , "More detailed help can then be obtained by running the :help command"
        , "with another command as an argument, e.g."
        , "  > :help :help"
        , "  > :help :set"
        , "(the leading ':' in the command argument is optional)"
        ] ) ++
  [ ( "let"
    , """
      Define a new value.

      First, declare the type of your new value, e.g.
        :let myValue : List Nat

      Then, define the value:
        :let myValue = [1, 2, 3]

      Now the value is in scope at the REPL:
        > map (+ 2) myValue
        [3, 4, 5]
      """
    )
  ] ++
  explain ["fs", "fsearch"] "Search for global definitions by sketching the names distribution of the wanted type(s)."
  where
    explain : List String -> String -> List (String, String)
    explain cmds expl = map (\s => (s, expl)) cmds

public export
KnownCommand : String -> Type
KnownCommand cmd = IsJust (lookup cmd knownCommands)

export
data ParseCmd : Type where
     ParseREPLCmd :  (cmds : List String)
                  -> {auto 0 _ : All KnownCommand cmds}
                  -> ParseCmd

     ParseKeywordCmd :  (cmds : List String)
                     -> {auto 0 _ : All KnownCommand cmds}
                     -> ParseCmd

     ParseIdentCmd :  (cmd : String)
                   -> {auto 0 _ : KnownCommand cmd}
                   -> ParseCmd

public export
CommandDefinition : Type
CommandDefinition = (List String, CmdArg, String, Rule REPLCmd)

public export
CommandTable : Type
CommandTable = List CommandDefinition

extractNames : ParseCmd -> List String
extractNames (ParseREPLCmd names) = names
extractNames (ParseKeywordCmd keywords) = keywords
extractNames (ParseIdentCmd ident) = [ident]

runParseCmd : ParseCmd -> Rule ()
runParseCmd (ParseREPLCmd names) = replCmd names
runParseCmd (ParseKeywordCmd keywords) = choice $ map keyword keywords
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
      n <- mustWork name
      pure (command n)

stringArgCmd : ParseCmd -> (String -> REPLCmd) -> String -> CommandDefinition
stringArgCmd parseCmd command doc = (names, StringArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      s <- mustWork simpleStr
      pure (command s)

getHelpType : EmptyRule HelpType
getHelpType = do
  optCmd <- optional $ choice $ (cmdName . fst) <$> knownCommands
  pure $
    case optCmd of
         Nothing => GenericHelp
         Just cmd => DetailedHelp $ fromMaybe "Unrecognised command '\{cmd}'"
                                  $ lookup cmd knownCommands

helpCmd :  ParseCmd
        -> (HelpType -> REPLCmd)
        -> String
        -> CommandDefinition
helpCmd parseCmd command doc = (names, StringArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      helpType <- getHelpType
      pure (command helpType)

moduleArgCmd : ParseCmd -> (ModuleIdent -> REPLCmd) -> String -> CommandDefinition
moduleArgCmd parseCmd command doc = (names, ModuleArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      n <- mustWork moduleIdent
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
      tm <- mustWork $ typeExpr pdef (Virtual Interactive) init
      pure (command tm)

docArgCmd : ParseCmd -> (DocDirective -> REPLCmd) -> String -> CommandDefinition
docArgCmd parseCmd command doc = (names, DocArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    -- by default, lazy primitives must be followed by a simpleExpr, so we have
    -- this custom parser for the doc case
    docLazyPrim : Rule PTerm
    docLazyPrim =
      let placeholeder : PTerm' Name
          placeholeder = PHole EmptyFC False "lazyDocPlaceholeder"
      in  do exactIdent "Lazy"    -- v
             pure (PDelayed EmptyFC LLazy placeholeder)
      <|> do exactIdent "Inf"     -- v
             pure (PDelayed EmptyFC LInf placeholeder)
      <|> do exactIdent "Delay"
             pure (PDelay EmptyFC placeholeder)
      <|> do exactIdent "Force"
             pure (PForce EmptyFC placeholeder)

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      dir <- mustWork $
        AModule <$ keyword "module" <*> moduleIdent -- must be before Keyword to not be captured
        <|> Keyword <$> anyKeyword
        <|> Symbol <$> (anyReservedSymbol <* eoi
                       <|> parens (Virtual Interactive) anyReservedSymbol <* eoi)
        <|> Bracket <$> (
              IdiomBrackets <$ symbol "[|" <* symbol "|]"
              <|> NameQuote <$ symbol "`{" <* symbol "}"
              <|> TermQuote <$ symbol "`(" <* symbol ")"
              <|> DeclQuote <$ symbol "`[" <* symbol "]"
              )
        <|> APTerm <$> (
              docLazyPrim
              <|> typeExpr pdef (Virtual Interactive) init
              )
      pure (command dir)

declsArgCmd : ParseCmd -> (List PDecl -> REPLCmd) -> String -> CommandDefinition
declsArgCmd parseCmd command doc = (names, DeclsArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd
    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      tm <- mustWork $ topDecl (Virtual Interactive) init
      pure (command [tm])

optArgCmd : ParseCmd -> (REPLOpt -> REPLCmd) -> Bool -> String -> CommandDefinition
optArgCmd parseCmd command set doc = (names, OptionArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      opt <- mustWork $ setOption set
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
      i <- mustWork intLit
      pure (command (fromInteger i))

autoNumberArgCmd : ParseCmd -> (Maybe Nat -> REPLCmd) -> String -> CommandDefinition
autoNumberArgCmd parseCmd command doc = (names, AutoNumberArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    autoNumber : Rule (Maybe Nat)
    autoNumber = Nothing <$ keyword "auto"
             <|> Just . fromInteger <$> intLit

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      mi <- mustWork autoNumber
      pure (command mi)

onOffArgCmd : ParseCmd -> (Bool -> REPLCmd) -> String -> CommandDefinition
onOffArgCmd parseCmd command doc = (names, OnOffArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      i <- mustWork onOffLit
      pure (command i)

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
      n <- mustWork unqualifiedName
      tm <- mustWork $ expr pdef (Virtual Interactive) init
      pure (command tm n)

loggingArgCmd : ParseCmd -> (Maybe LogLevel -> REPLCmd) -> String -> CommandDefinition
loggingArgCmd parseCmd command doc = (names, Args [StringArg, NumberArg], doc, parse) where

  names : List String
  names = extractNames parseCmd

  parse : Rule REPLCmd
  parse = do
    symbol ":"
    runParseCmd parseCmd
    lvl <- mustWork $ logLevel (Virtual Interactive)
    pure (command lvl)

editLineNameArgCmd : ParseCmd -> (Bool -> Int -> Name -> EditCmd) -> String -> CommandDefinition
editLineNameArgCmd parseCmd command doc = (names, Args [NamedCmdArg "l" NumberArg, NamedCmdArg "n" StringArg], doc, parse) where

  names : List String
  names = extractNames parseCmd

  parse : Rule REPLCmd
  parse = do
    symbol ":"
    runParseCmd parseCmd
    upd <- option False (symbol "!" $> True)
    line <- fromInteger <$> mustWork intLit
    n <- mustWork name
    pure (Editing $ command upd line n)

editLineColNameArgCmd : ParseCmd -> (Bool -> Int -> Int -> Name -> EditCmd) -> String -> CommandDefinition
editLineColNameArgCmd parseCmd command doc =
  ( names
  , Args [ NamedCmdArg "l" NumberArg
         , NamedCmdArg "c" NumberArg
         , NamedCmdArg "n" StringArg
         ]
  , doc
  , parse
  ) where

  names : List String
  names = extractNames parseCmd

  parse : Rule REPLCmd
  parse = do
    symbol ":"
    runParseCmd parseCmd
    upd <- option False (symbol "!" $> True)
    line <- fromInteger <$> mustWork intLit
    col <- fromInteger <$> mustWork intLit
    n <- mustWork name
    pure (Editing $ command upd line col n)

editLineNamePTermArgCmd : ParseCmd -> (Bool -> Int -> Name -> PTerm -> EditCmd) -> String -> CommandDefinition
editLineNamePTermArgCmd parseCmd command doc =
  ( names
  , Args [ NamedCmdArg "l" NumberArg
         , NamedCmdArg "h" StringArg
         , NamedCmdArg "e" ExprArg
         ]
  , doc
  , parse
  ) where

  names : List String
  names = extractNames parseCmd

  parse : Rule REPLCmd
  parse = do
    symbol ":"
    runParseCmd parseCmd
    upd <- option False (symbol "!" $> True)
    line <- fromInteger <$> mustWork intLit
    h <- mustWork name
    n <- mustWork $ typeExpr pdef (Virtual Interactive) init
    pure (Editing $ command upd line h n)

editLineNameCSVArgCmd : ParseCmd
                       -> (Bool -> Int -> Name -> List Name -> EditCmd)
                       -> String
                       -> CommandDefinition
editLineNameCSVArgCmd parseCmd command doc =
  ( names
  , Args [ NamedCmdArg "l" NumberArg
         , NamedCmdArg "n" StringArg
         , NamedCmdArg "h" (CSVArg NameArg)
         ]
  , doc
  , parse
  ) where

  names : List String
  names = extractNames parseCmd

  parse : Rule REPLCmd
  parse = do
    symbol ":"
    runParseCmd parseCmd
    upd <- option False (symbol "!" $> True)
    line <- fromInteger <$> mustWork intLit
    n <- mustWork name
    hints <- mustWork $ sepBy (symbol ",") name
    pure (Editing $ command upd line n hints)

editLineNameOptionArgCmd : ParseCmd
                        -> (Bool -> Int -> Name -> Nat -> EditCmd)
                        -> String
                        -> CommandDefinition
editLineNameOptionArgCmd parseCmd command doc =
  ( names
  , Args [ NamedCmdArg "l" NumberArg
         , NamedCmdArg "n" StringArg
         , NamedCmdArg "r" (WithDefaultArg "0" NumberArg)
         ]
  , doc
  , parse
  ) where

  names : List String
  names = extractNames parseCmd

  parse : Rule REPLCmd
  parse = do
    symbol ":"
    runParseCmd parseCmd
    upd <- option False (symbol "!" $> True)
    line <- fromInteger <$> mustWork intLit
    n <- mustWork name
    nreject <- fromInteger <$> option 0 intLit
    pure (Editing $ command upd line n nreject)

firstHelpLine : (cmd : String) -> {auto 0 _ : KnownCommand cmd} -> String
firstHelpLine cmd =
  head . (split ((==) '\n')) $
  fromMaybe "Failed to look up '\{cmd}' (SHOULDN'T HAPPEN!)" $
  lookup cmd knownCommands

export
parserCommandsForHelp : CommandTable
parserCommandsForHelp =
  [ exprArgCmd (ParseREPLCmd ["t", "type"]) Check (firstHelpLine "t")
  , exprArgCmd (ParseREPLCmd ["ti"]) CheckWithImplicits (firstHelpLine "ti")
  , exprArgCmd (ParseREPLCmd ["printdef"]) PrintDef (firstHelpLine "printdef")
  , exprArgCmd (ParseREPLCmd ["s", "search"]) TypeSearch (firstHelpLine "s")
  , nameArgCmd (ParseIdentCmd "di") DebugInfo (firstHelpLine "di")
  , moduleArgCmd (ParseKeywordCmd ["module", "import"]) ImportMod (firstHelpLine "module")
  , stringArgCmd (ParseREPLCmd ["package"]) ImportPackage (firstHelpLine "package")
  , noArgCmd (ParseREPLCmd ["q", "quit", "exit"]) Quit (firstHelpLine "q")
  , noArgCmd (ParseREPLCmd ["cwd"]) CWD (firstHelpLine "cwd")
  , stringArgCmd (ParseREPLCmd ["cd"]) CD (firstHelpLine "cd")
  , stringArgCmd (ParseREPLCmd ["sh"]) RunShellCommand (firstHelpLine "sh")
  , optArgCmd (ParseIdentCmd "set") SetOpt True (firstHelpLine "set")
  , optArgCmd (ParseIdentCmd "unset") SetOpt False (firstHelpLine "unset")
  , noArgCmd (ParseREPLCmd ["opts"]) GetOpts (firstHelpLine "opts")
  , compileArgsCmd (ParseREPLCmd ["c", "compile"]) Compile (firstHelpLine "c")
  , exprArgCmd (ParseIdentCmd "exec") Exec (firstHelpLine "exec")
  , stringArgCmd (ParseIdentCmd "directive") CGDirective (firstHelpLine "directive")
  , stringArgCmd (ParseREPLCmd ["l", "load"]) Load (firstHelpLine "l")
  , noArgCmd (ParseREPLCmd ["r", "reload"]) Reload (firstHelpLine "r")
  , noArgCmd (ParseREPLCmd ["e", "edit"]) Edit (firstHelpLine "e")
  , nameArgCmd (ParseREPLCmd ["miss", "missing"]) Missing (firstHelpLine "miss")
  , nameArgCmd (ParseKeywordCmd ["total"]) Total (firstHelpLine "total")
  , docArgCmd (ParseIdentCmd "doc") Doc (firstHelpLine "doc")
  , moduleArgCmd (ParseIdentCmd "browse") (Browse . miAsNamespace) (firstHelpLine "browse")
  , loggingArgCmd (ParseREPLCmd ["log", "logging"]) SetLog (firstHelpLine "log")
  , autoNumberArgCmd (ParseREPLCmd ["consolewidth"]) SetConsoleWidth (firstHelpLine "consolewidth")
  , onOffArgCmd (ParseREPLCmd ["colour", "color"]) SetColor (firstHelpLine "colour")
  , noArgCmd (ParseREPLCmd ["m", "metavars"]) Metavars (firstHelpLine "m")
  , editLineColNameArgCmd (ParseREPLCmd ["typeat"]) (const TypeAt) (firstHelpLine "typeat")
  , editLineColNameArgCmd (ParseREPLCmd ["cs", "casesplit"]) CaseSplit (firstHelpLine "cs")
  , editLineNameArgCmd (ParseREPLCmd ["ac", "addclause"]) AddClause (firstHelpLine "ac")
  , editLineNameArgCmd (ParseREPLCmd ["ml", "makelemma"]) MakeLemma (firstHelpLine "ml")
  , editLineNameArgCmd (ParseREPLCmd ["mc", "makecase"]) MakeCase (firstHelpLine "mc")
  , editLineNameArgCmd (ParseREPLCmd ["mw", "makewith"]) MakeWith (firstHelpLine "mw")
  , editLineNameArgCmd (ParseREPLCmd ["intro"]) Intro (firstHelpLine "intro")
  , editLineNamePTermArgCmd (ParseREPLCmd ["refine"]) Refine (firstHelpLine "refine")
  , editLineNameCSVArgCmd (ParseREPLCmd ["ps", "proofsearch"]) ExprSearch (firstHelpLine "ps")
  , noArgCmd (ParseREPLCmd ["psnext"]) (Editing ExprSearchNext) (firstHelpLine "psnext")
  , editLineNameOptionArgCmd (ParseREPLCmd ["gd"]) GenerateDef (firstHelpLine "gd")
  , noArgCmd (ParseREPLCmd ["gdnext"]) (Editing GenerateDefNext) (firstHelpLine "gdnext")
  , noArgCmd (ParseREPLCmd ["version"]) ShowVersion (firstHelpLine "version")
  , helpCmd (ParseREPLCmd ["?", "h", "help"]) Help (firstHelpLine "?")
  , declsArgCmd (ParseKeywordCmd ["let"]) NewDefn (firstHelpLine "let")
  , exprArgCmd (ParseREPLCmd ["fs", "fsearch"]) FuzzyTypeSearch (firstHelpLine "fs")
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
  tm <- typeExpr pdef (Virtual Interactive) init
  pure (Eval tm)

export
aPTerm : Rule PTerm
aPTerm = typeExpr pdef (Virtual Interactive) init

export
command : EmptyRule REPLCmd
command
    = eoi $> NOP
  <|> nonEmptyCommand
  <|> (do symbol ":?" -- special case, :? doesn't fit into above scheme
          helpType <- getHelpType
          pure $ Help helpType)
  <|> eval
