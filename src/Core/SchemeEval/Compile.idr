module Core.SchemeEval.Compile

{- TODO:

- Make a decent set of test cases
- Option to keep vs discard FCs for faster quoting where we don't need FC

Advanced TODO (possibly not worth it...):
- Write a conversion check
- Extend unification to use SObj; include SObj in Glued

-}

import Core.Case.CaseTree
import Core.Context
import Core.Core
import Core.Directory
import Core.SchemeEval.Builtins
import Core.SchemeEval.ToScheme
import Core.TT

import Data.List

import Libraries.Utils.Scheme
import System.Info

import Libraries.Data.WithDefault

schString : String -> String
schString s = concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar c = if isAlphaNum c || c =='_'
                  then cast c
                  else "C-" ++ show (cast {to=Int} c)

schVarUN : UserName -> String
schVarUN (Basic n) = schString n
schVarUN (Field n) = "rf--" ++ schString n
schVarUN Underscore = "_US_"

schVarName : Name -> String
schVarName (NS ns (UN n))
   = schString (showNSWithSep "-" ns) ++ "-" ++ schVarUN n
schVarName (NS ns n) = schString (showNSWithSep "-" ns) ++ "-" ++ schVarName n
schVarName (UN n) = "u--" ++ schVarUN n
schVarName (MN n i) = schString n ++ "-" ++ show i
schVarName (PV n d) = "pat--" ++ schVarName n
schVarName (DN _ n) = schVarName n
schVarName (Nested (i, x) n) = "n--" ++ show i ++ "-" ++ show x ++ "-" ++ schVarName n
schVarName (CaseBlock x y) = "case--" ++ schString x ++ "-" ++ show y
schVarName (WithBlock x y) = "with--" ++ schString x ++ "-" ++ show y
schVarName (Resolved i) = "fn--" ++ show i

schName : Name -> String
schName n = "ct-" ++ schVarName n

export
data Sym : Type where

export
nextName : Ref Sym Integer => Core Integer
nextName
    = do n <- get Sym
         put Sym (n + 1)
         pure n

public export
data SVar = Bound String | Free String

Show SVar where
  show (Bound x) = x
  show (Free x) = "'" ++ x

export
getName : SVar -> String
getName (Bound x) = x
getName (Free x) = x

public export
data SchVars : SnocList Name -> Type where
     Nil : SchVars [<]
     (::) : SVar -> SchVars ns -> SchVars (n :%: ns)

Show (SchVars ns) where
  show xs = show (toList xs)
    where
      toList : forall ns . SchVars ns -> List String
      toList [] = []
      toList (Bound x :: xs) = x :: toList xs
      toList (Free x :: xs) = "'x" :: toList xs

getSchVar : {idx : _} -> (0 _ : IsVar n idx vars) -> SchVars vars -> String
getSchVar First (Bound x :: xs) = x
getSchVar First (Free x :: xs) = "'" ++ x
getSchVar (Later p) (x :: xs) = getSchVar p xs

{-

Encoding of NF -> Scheme

Maybe consider putting this back into a logical order, rather than the order
I implemented them in...

vector (tag>=0) name args == data constructor
vector (-10) (name, arity) (args as list) == blocked meta application
                   (needs to be same arity as block app, for ct-addArg)
vector (-11) symbol (args as list) == blocked local application
vector (-1) ... == type constructor
vector (-2) name (args as list) == blocked application
vector (-3) ... == Pi binder
vector (-4) ... == delay arg
vector (-5) ... == force arg
vector (-6) = Erased
vector (-7) = Type
vector (-8) ... = Lambda
vector (-9) blockedapp proc = Top level lambda (from a PMDef, so not expanded)
vector (-12) ... = PVar binding
vector (-13) ... = PVTy binding
vector (-14) ... = PLet binding
vector (-15) ... = Delayed

vector (-100 onwards) ... = constants
-}

blockedAppWith : Name -> List (SchemeObj Write) -> SchemeObj Write
blockedAppWith n args = Vector (-2) [toScheme n, vars args]
  where
    vars : List (SchemeObj Write) -> SchemeObj Write
    vars [] = Null
    vars (x :: xs) = Cons x (vars xs)

blockedMetaApp : Name -> SchemeObj Write
blockedMetaApp n
    = Lambda ["arity-0"] (Vector (-10) [Cons (toScheme n) (Var "arity-0"),
                                        Null])

unload : SchemeObj Write -> List (SchemeObj Write) -> SchemeObj Write
unload f [] = f
unload f (a :: as) = unload (Apply (Var "ct-app") [f, a]) as

compileConstant : FC -> Constant -> SchemeObj Write
compileConstant fc (I x) = Vector (-100) [IntegerVal (cast x)]
compileConstant fc (I8 x) = Vector (-101) [IntegerVal (cast x)]
compileConstant fc (I16 x) = Vector (-102) [IntegerVal (cast x)]
compileConstant fc (I32 x) = Vector (-103) [IntegerVal (cast x)]
compileConstant fc (I64 x) = Vector (-104) [IntegerVal (cast x)]
compileConstant fc (BI x) = Vector (-105) [IntegerVal x]
compileConstant fc (B8 x) = Vector (-106) [IntegerVal (cast x)]
compileConstant fc (B16 x) = Vector (-107) [IntegerVal (cast x)]
compileConstant fc (B32 x) = Vector (-108) [IntegerVal (cast x)]
compileConstant fc (B64 x) = Vector (-109) [IntegerVal (cast x)]
compileConstant fc (Str x) = StringVal x
compileConstant fc (Ch x) = CharVal x
compileConstant fc (Db x) = FloatVal x
compileConstant fc (PrT t) -- Constant types get compiled as TyCon names, for matching purposes
    = Vector (-1) [IntegerVal (cast (primTypeTag t)),
                   StringVal (show t),
                   toScheme (UN (Basic (show t))),
                   toScheme fc]
compileConstant fc WorldVal = Null

compileStk : Ref Sym Integer =>
             {auto c : Ref Ctxt Defs} ->
             SchVars vars -> List (SchemeObj Write) -> Term vars ->
             Core (SchemeObj Write)

compilePiInfo : Ref Sym Integer =>
                {auto c : Ref Ctxt Defs} ->
                SchVars vars -> PiInfo (Term vars) ->
                Core (PiInfo (SchemeObj Write))
compilePiInfo svs Implicit = pure Implicit
compilePiInfo svs Explicit = pure Explicit
compilePiInfo svs AutoImplicit = pure AutoImplicit
compilePiInfo svs (DefImplicit t)
    = do t' <- compileStk svs [] t
         pure (DefImplicit t')

compileWhyErased : Ref Sym Integer =>
                {auto c : Ref Ctxt Defs} ->
                SchVars vars -> List (SchemeObj Write) -> WhyErased (Term vars) ->
                Core (WhyErased (SchemeObj Write))
compileWhyErased svs stk Impossible = pure Impossible
compileWhyErased svs stk Placeholder = pure Placeholder
compileWhyErased svs stk (Dotted t)
    = do t' <- compileStk svs stk t
         pure (Dotted t')

compileStk svs stk (Local fc isLet idx p)
    = pure $ unload (Var (getSchVar p svs)) stk
-- We are assuming that the bound name is a valid scheme symbol. We should
-- only see this when inventing temporary names during quoting
compileStk svs stk (Ref fc Bound name)
    = pure $ unload (Symbol (show name)) stk
compileStk svs stk (Ref fc (DataCon t a) name)
    = if length stk == a -- inline it if it's fully applied
         then pure $ Vector (cast t)
                       (toScheme !(toResolvedNames name) ::
                        toScheme fc :: stk)
         else pure $ unload (Apply (Var (schName name)) []) stk
compileStk svs stk (Ref fc (TyCon t a) name)
    = if length stk == a -- inline it if it's fully applied
         then pure $ Vector (-1)
                       (IntegerVal (cast t) ::
                        StringVal (show name) ::
                        toScheme !(toResolvedNames name) ::
                        toScheme fc :: stk)
         else pure $ unload (Apply (Var (schName name)) []) stk
compileStk svs stk (Ref fc x name)
    = pure $ unload (Apply (Var (schName name)) []) stk
compileStk svs stk (Meta fc name i xs)
    = do xs' <- traverse (compileStk svs stk) xs
         -- we encode the arity as first argument to the hole definition, which
         -- helps in readback, so we have to apply the hole function to the
         -- length of xs to be able to restore the Meta properly
         pure $ unload (Apply (Var (schName name)) [])
                       (IntegerVal (cast (length xs)) :: stk ++ xs')
compileStk svs stk (Bind fc x (Let _ _ val _) scope)
    = do i <- nextName
         let x' = schVarName x ++ "-" ++ show i
         val' <- compileStk svs [] val
         sc' <- compileStk (Bound x' :: svs) [] scope
         pure $ unload (Let x' val' sc') stk
compileStk svs stk (Bind fc x (Pi _ rig p ty) scope)
    = do i <- nextName
         let x' = schVarName x ++ "-" ++ show i
         ty' <- compileStk svs [] ty
         sc' <- compileStk (Bound x' :: svs) [] scope
         p' <- compilePiInfo svs p
         pure $ Vector (-3) [Lambda [x'] sc', toScheme rig, toSchemePi p',
                                              ty', toScheme x]
compileStk svs stk (Bind fc x (PVar _ rig p ty) scope)
    = do i <- nextName
         let x' = schVarName x ++ "-" ++ show i
         ty' <- compileStk svs [] ty
         sc' <- compileStk (Bound x' :: svs) [] scope
         p' <- compilePiInfo svs p
         pure $ Vector (-12) [Lambda [x'] sc', toScheme rig, toSchemePi p',
                                               ty', toScheme x]
compileStk svs stk (Bind fc x (PVTy _ rig ty) scope)
    = do i <- nextName
         let x' = schVarName x ++ "-" ++ show i
         ty' <- compileStk svs [] ty
         sc' <- compileStk (Bound x' :: svs) [] scope
         pure $ Vector (-13) [Lambda [x'] sc', toScheme rig, ty', toScheme x]
compileStk svs stk (Bind fc x (PLet _ rig val ty) scope) -- we only see this on LHS
    = do i <- nextName
         let x' = schVarName x ++ "-" ++ show i
         val' <- compileStk svs [] val
         ty' <- compileStk svs [] ty
         sc' <- compileStk (Bound x' :: svs) [] scope
         pure $ Vector (-14) [Lambda [x'] sc', toScheme rig, val', ty', toScheme x]
compileStk svs [] (Bind fc x (Lam _ rig p ty) scope)
    = do i <- nextName
         let x' = schVarName x ++ "-" ++ show i
         ty' <- compileStk svs [] ty
         sc' <- compileStk (Bound x' :: svs) [] scope
         p' <- compilePiInfo svs p
         pure $ Vector (-8) [Lambda [x'] sc', toScheme rig, toSchemePi p',
                                              ty', toScheme x]
compileStk svs (s :: stk) (Bind fc x (Lam _ _ _ _) scope)
    = do i <- nextName
         let x' = schVarName x ++ "-" ++ show i
         sc' <- compileStk (Bound x' :: svs) stk scope
         pure $ Apply (Lambda [x'] sc') [s]
compileStk svs stk (App fc fn arg)
    = compileStk svs (!(compileStk svs [] arg) :: stk) fn
-- We're only using this evaluator for REPL and typechecking, not for
-- tidying up definitions or LHSs, so we'll always remove As patterns
compileStk svs stk (As fc x as pat) = compileStk svs stk pat
compileStk svs stk (TDelayed fc r ty)
    = do ty' <- compileStk svs stk ty
         pure $ Vector (-15) [toScheme r, ty']
compileStk svs stk (TDelay fc r ty arg)
    = do ty' <- compileStk svs [] ty
         arg' <- compileStk svs [] arg
         pure $ Vector (-4) [toScheme r, toScheme fc,
                             Lambda [] ty', Lambda [] arg']
compileStk svs stk (TForce fc x tm)
    = do tm' <- compileStk svs [] tm
         pure $ Apply (Var "ct-doForce")
                      [tm',
                      Vector (-5) [toScheme x, toScheme fc, Lambda [] tm']]
compileStk svs stk (PrimVal fc c) = pure $ compileConstant fc c
compileStk svs stk (Erased fc why)
  = do why' <- compileWhyErased svs stk why
       pure $ Vector (-6) [toScheme fc, toSchemeWhy why']
compileStk svs stk (TType fc u) = pure $ Vector (-7) [toScheme fc, toScheme u]

export
compile : Ref Sym Integer =>
          {auto c : Ref Ctxt Defs} ->
          SchVars vars -> Term vars -> Core (SchemeObj Write)
compile vars tm = compileStk vars [] tm

getArgName : Ref Sym Integer =>
             Core Name
getArgName
    = do i <- nextName
         pure (MN "carg" (cast i))

extend : Ref Sym Integer =>
         (args : SnocList Name) -> SchVars vars ->
         Core (List Name, SchVars (vars ++ args))
extend [<] svs = pure ([], svs)
extend (arg :%: args) svs
    = do n <- getArgName
         (args', svs') <- extend args svs
         pure (n :: args', Bound (schVarName n) :: svs')

compileCase : Ref Sym Integer =>
              {auto c : Ref Ctxt Defs} ->
              (blocked : SchemeObj Write) ->
              SchVars vars -> CaseTree vars -> Core (SchemeObj Write)
compileCase blk svs (Case idx p scTy xs)
    = case !(caseType xs) of
           CON => toSchemeConCases idx p xs
           TYCON => toSchemeTyConCases idx p xs
           DELAY => toSchemeDelayCases idx p xs
           CONST => toSchemeConstCases idx p xs
  where
    data CaseType = CON | TYCON | DELAY | CONST

    caseType : List (CaseAlt vs) -> Core CaseType
    caseType [] = pure CON
    caseType (ConCase x tag args y :: xs)
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact x (gamma defs)
                  | Nothing => pure TYCON -- primitive type match
             case definition gdef of
                  DCon{} => pure CON
                  TCon{} => pure TYCON
                  _ => pure CON -- or maybe throw?
    caseType (DelayCase ty arg x :: xs) = pure DELAY
    caseType (ConstCase x y :: xs) = pure CONST
    caseType (DefaultCase x :: xs) = caseType xs

    makeDefault : List (CaseAlt vars) -> Core (SchemeObj Write)
    makeDefault [] = pure blk
    makeDefault (DefaultCase sc :: xs) = compileCase blk svs sc
    makeDefault (_ :: xs) = makeDefault xs

    toSchemeConCases : (idx : Nat) -> (0 p : IsVar n idx vars) ->
                       List (CaseAlt vars) -> Core (SchemeObj Write)
    toSchemeConCases idx p alts
        = do let var = getSchVar p svs
             alts' <- traverse (makeAlt var) alts
             let caseblock
                    = Case (Apply (Var "vector-ref") [Var var, IntegerVal 0])
                           (mapMaybe id alts')
                           (Just !(makeDefault alts))
             pure $ If (Apply (Var "ct-isDataCon") [Var var])
                       caseblock
                       blk
      where
        project : Int -> String -> List Name ->
                  SchemeObj Write -> SchemeObj Write
        project i var [] body = body
        project i var (n :: ns) body
            = Let (schVarName n)
                  (Apply (Var "vector-ref") [Var var, IntegerVal (cast i)])
                  (project (i + 1) var ns body)

        bindArgs : String -> (args : SnocList Name) -> CaseTree (vars ++ args) ->
                   Core (SchemeObj Write)
        bindArgs var args sc
            = do (bind, svs') <- extend args svs
                 project 3 var bind <$> compileCase blk svs' sc

        makeAlt : String -> CaseAlt vars ->
                  Core (Maybe (SchemeObj Write, SchemeObj Write))
        makeAlt var (ConCase n t args sc)
            = pure $ Just (IntegerVal (cast t), !(bindArgs var args sc))
        -- TODO: Matching on types, including ->
        makeAlt var _ = pure Nothing

    toSchemeTyConCases : (idx : Nat) -> (0 p : IsVar n idx vars) ->
                         List (CaseAlt vars) -> Core (SchemeObj Write)
    toSchemeTyConCases idx p alts
        = do let var = getSchVar p svs
             alts' <- traverse (makeAlt var) alts
             caseblock <- addPiMatch var alts
                      -- work on the name, so the 2nd arg
                            (Case (Apply (Var "vector-ref") [Var var, IntegerVal 2])
                               (mapMaybe id alts')
                               (Just !(makeDefault alts)))
             pure $ If (Apply (Var "ct-isTypeMatchable") [Var var])
                       caseblock
                       blk
      where
        project : Int -> String -> List Name ->
                  SchemeObj Write -> SchemeObj Write
        project i var [] body = body
        project i var (n :: ns) body
            = Let (schVarName n)
                  (Apply (Var "vector-ref") [Var var, IntegerVal (cast i)])
                  (project (i + 1) var ns body)

        bindArgs : String -> (args : SnocList Name) -> CaseTree (vars ++ args) ->
                   Core (SchemeObj Write)
        bindArgs var args sc
            = do (bind, svs') <- extend args svs
                 project 5 var bind <$> compileCase blk svs' sc

        makeAlt : String -> CaseAlt vars ->
                  Core (Maybe (SchemeObj Write, SchemeObj Write))
        makeAlt var (ConCase (UN (Basic "->")) t (_ :%: _ :%: [<]) sc)
            = pure Nothing -- do this in 'addPiMatch' below, since the
                           -- representation is different
        makeAlt var (ConCase n t args sc)
            = pure $ Just (StringVal (show n), !(bindArgs var args sc))
        makeAlt var _ = pure Nothing

        addPiMatch : String -> List (CaseAlt vars) -> SchemeObj Write ->
                     Core (SchemeObj Write)
        addPiMatch var [] def = pure def
        -- t is a function type, and conveniently the scope of a pi
        -- binding is represented as a function. Lucky us! So we just need
        -- to extract it then evaluate the scope
        addPiMatch var (ConCase (UN (Basic "->")) _ (s :%: t :%: [<]) sc :: _) def
            = do sn <- getArgName
                 tn <- getArgName
                 let svs' = Bound (schVarName sn) ::
                              Bound (schVarName tn) :: svs
                 sc' <- compileCase blk svs' sc
                 pure $ If (Apply (Var "ct-isPi") [Var var])
                           (Let (schVarName sn) (Apply (Var "vector-ref") [Var var, IntegerVal 4]) $
                            Let (schVarName tn) (Apply (Var "vector-ref") [Var var, IntegerVal 1]) $
                            sc')
                           def
        addPiMatch var (x :: xs) def = addPiMatch var xs def

    toSchemeConstCases : (idx : Nat) -> (0 p : IsVar n idx vars) ->
                         List (CaseAlt vars) -> Core (SchemeObj Write)
    toSchemeConstCases x p alts
        = do let var = getSchVar p svs
             alts' <- traverse (makeAlt var) alts
             let caseblock
                    = Cond (mapMaybe id alts')
                           (Just !(makeDefault alts))
             pure $ If (Apply (Var "ct-isConstant") [Var var])
                       caseblock
                       blk
     where
        makeAlt : String -> CaseAlt vars ->
                  Core (Maybe (SchemeObj Write, SchemeObj Write))
        makeAlt var (ConstCase c sc)
            = do sc' <- compileCase blk svs sc
                 pure (Just (Apply (Var "equal?")
                               [Var var, compileConstant emptyFC c], sc'))
        makeAlt var _ = pure Nothing

    toSchemeDelayCases : (idx : Nat) -> (0 p : IsVar n idx vars) ->
                         List (CaseAlt vars) -> Core (SchemeObj Write)
    -- there will only ever be one, or a default case
    toSchemeDelayCases idx p (DelayCase ty arg sc :: rest)
        = do let var = getSchVar p svs
             tyn <- getArgName
             argn <- getArgName
             let svs' = Bound (schVarName tyn) ::
                          Bound (schVarName argn) :: svs
             sc' <- compileCase blk svs' sc
             pure $ If (Apply (Var "ct-isDelay") [Var var])
                       (Let (schVarName tyn)
                           (Apply (Apply (Var "vector-ref") [Var var, IntegerVal 3]) []) $
                        Let (schVarName argn)
                           (Apply (Apply (Var "vector-ref") [Var var, IntegerVal 4]) []) $
                         sc')
                       blk
    toSchemeDelayCases idx p (_ :: rest) = toSchemeDelayCases idx p rest
    toSchemeDelayCases idx p _ = pure Null

compileCase blk vars (STerm _ tm) = compile vars tm
compileCase blk vars _ = pure blk

varObjs : SchVars ns -> List (SchemeObj Write)
varObjs [] = []
varObjs (x :: xs) = Var (show x) :: varObjs xs

mkArgs : (ns : SnocList Name) -> Core (SchVars ns)
mkArgs [<] = pure []
mkArgs (x :%: xs)
    = pure $ Bound (schVarName x) :: !(mkArgs xs)

bindArgs : Name ->
           (todo : SchVars ns) ->
           (done : List (SchemeObj Write)) ->
           SchemeObj Write -> SchemeObj Write
bindArgs n [] done body = body
bindArgs n (x :: xs) done body
    = Vector (-9) [blockedAppWith n (reverse done),
                   Lambda [show x]
                      (bindArgs n xs (Var (show x) :: done) body)]

compileBody : {auto c : Ref Ctxt Defs} ->
              Bool -> -- okay to reduce (if False, block)
              Name -> Def -> Core (SchemeObj Write)
compileBody _ n None = pure $ blockedAppWith n []
compileBody redok n (PMDef pminfo args treeCT treeRT pats)
    = do i <- newRef Sym 0
         argvs <- mkArgs args
         let blk = blockedAppWith n (varObjs argvs)
         body <- compileCase blk argvs treeCT
         let body' = if redok
                        then If (Apply (Var "ct-isBlockAll") []) blk body
                        else blk
         -- If it arose from a hole, we need to take an extra argument for
         -- the arity since that's what Meta gets applied to
         case holeInfo pminfo of
              NotHole => pure (bindArgs n argvs [] body')
              SolvedHole _ => pure (Lambda ["h-0"] (bindArgs n argvs [] body'))
compileBody _ n (ExternDef arity) = pure $ blockedAppWith n []
compileBody _ n (ForeignDef arity xs) = pure $ blockedAppWith n []
compileBody _ n (Builtin x) = pure $ compileBuiltin n x
compileBody _ n (DCon tag Z newtypeArg)
    = pure $ Vector (cast tag) [toScheme !(toResolvedNames n), toScheme emptyFC]
compileBody _ n (DCon tag arity newtypeArg)
    = do let args = mkArgNs 0 arity
         argvs <- mkArgs args
         let body
               = Vector (cast tag)
                        (toScheme n :: toScheme emptyFC ::
                             map (Var . schVarName) (toList args))
         pure (bindArgs n argvs [] body)
  where
    mkArgNs : Int -> Nat -> SnocList Name
    mkArgNs i Z = [<]
    mkArgNs i (S k) = MN "arg" i :%: mkArgNs (i+1) k
compileBody _ n (TCon tag Z parampos detpos flags mutwith datacons detagabbleBy)
    = pure $ Vector (-1) [IntegerVal (cast tag), StringVal (show n),
                          toScheme n, toScheme emptyFC]
compileBody _ n (TCon tag arity parampos detpos flags mutwith datacons detagabbleBy)
    = do let args = mkArgNs 0 arity
         argvs <- mkArgs args
         let body
               = Vector (-1)
                        (IntegerVal (cast tag) ::
                         StringVal (show n) ::
                          toScheme n :: toScheme emptyFC ::
                            map (Var . schVarName) (toList args))
         pure (bindArgs n argvs [] body)
  where
    mkArgNs : Int -> Nat -> SnocList Name
    mkArgNs i Z = [<]
    mkArgNs i (S k) = MN "arg" i :%: mkArgNs (i+1) k
compileBody _ n (Hole numlocs x) = pure $ blockedMetaApp n
compileBody _ n (BySearch x maxdepth defining) = pure $ blockedMetaApp n
compileBody _ n (Guess guess envbind constraints) = pure $ blockedMetaApp n
compileBody _ n ImpBind = pure $ blockedMetaApp n
compileBody _ n (UniverseLevel _) = pure $ blockedMetaApp n
compileBody _ n Delayed = pure $ blockedMetaApp n

export
compileDef : {auto c : Ref Ctxt Defs} -> SchemeMode -> Name -> Core ()
compileDef mode n_in
    = do n <- toFullNames n_in -- this is handy for readability of generated names
                     -- we used resolved names for blocked names, though, as
                     -- that's a bit better for performance
         defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (UndefinedName emptyFC n)

         let True = case schemeExpr def of
                         Nothing => True
                         Just (cmode, def) => cmode /= mode
               | _ => pure () -- already done
         -- If we're in BlockExport mode, check whether the name is
         -- available for reduction.
         let redok = mode == EvalAll ||
                       reducibleInAny (currentNS defs :: nestedNS defs)
                                      (fullname def)
                                      (collapseDefault $ visibility def)
         -- 'n' is used in compileBody for generating names for readback,
         -- and reading back resolved names is quicker because it's just
         -- an integer
         b <- compileBody redok !(toResolvedNames n) !(toFullNames (definition def))
         let schdef = Define (schName n) b

         -- Add the new definition to the current scheme runtime
         Just obj <- coreLift $ evalSchemeObj schdef
              | Nothing => throw (InternalError ("Compiling " ++ show n ++ " failed"))

         -- Record that this one is done
         ignore $ addDef n ({ schemeExpr := Just (mode, schdef) } def)

initEvalWith : {auto c : Ref Ctxt Defs} ->
               String -> Core Bool
initEvalWith "chez"
    = do defs <- get Ctxt
         if defs.schemeEvalLoaded
            then pure True
            else
             catch (do f <- readDataFile "chez/ct-support.ss"
                       Just _ <- coreLift $ evalSchemeStr $ "(begin " ++ f ++ ")"
                            | Nothing => pure False
                       put Ctxt ({ schemeEvalLoaded := True } defs)
                       pure True)
                (\err => pure False)
initEvalWith "racket"
    = do defs <- get Ctxt
         if defs.schemeEvalLoaded
            then pure True
            else
             catch (do f <- readDataFile "racket/ct-support.rkt"
                       Just _ <- coreLift $ evalSchemeStr $ "(begin " ++ f ++ ")"
                            | Nothing => pure False
                       put Ctxt ({ schemeEvalLoaded := True } defs)
                       pure True)
                (\err => do coreLift $ printLn err
                            pure False)
initEvalWith _ = pure False -- only works on Chez for now

-- Initialise the internal functions we need to build/extend blocked
-- applications
-- These are in a support file, chez/support.ss. Returns True if loading
-- and processing succeeds. If it fails, which it probably will during a
-- bootstrap build at least, we can fall back to the default evaluator.
export
initialiseSchemeEval : {auto c : Ref Ctxt Defs} ->
                       Core Bool
initialiseSchemeEval = initEvalWith codegen
