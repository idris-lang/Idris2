module Core.Normalise.Convert

import public Core.Normalise.Eval
import public Core.Normalise.Quote

import Core.Case.CaseTree
import Core.Context
import Core.Core
import Core.Env
import Core.TT
import Core.Value

import Data.List
import Data.SnocList

import Libraries.Data.List.SizeOf
import Libraries.Data.SnocList.HasLength
import Libraries.Data.SnocList.SizeOf

%default covering

extend : {args, args' : List Name} ->
     SizeOf args -> SizeOf args' ->
     (List (Var vars, Var vars')) ->
     Maybe (List (Var (Scope.ext vars args), Var (Scope.ext vars' args')))
extend s s' ms
  = do guard (size s == size s')
       let vs  = embedFishily @{ListFreelyEmbeddable} (Var.allVars (cast args))
       let vs' = embedFishily @{ListFreelyEmbeddable} (Var.allVars (cast args'))
       pure $ zip vs vs' ++ map (bimap (weakensN s) (weakensN s')) ms

findIdx : List (Var vars, Var vars') -> Nat -> Maybe (Var vars')
findIdx [] _ = Nothing
findIdx ((MkVar {varIdx = i} _, v) :: ps) n
    = if i == n then Just v else findIdx ps n

dropP : {0 args, args' : List Name} ->
  SizeOf args -> SizeOf args' ->
  (Var (Scope.ext vars args), Var (Scope.ext vars' args')) ->
  Maybe (Var vars, Var vars')
dropP s s' (x, y)
  = do x' <- strengthensN s x
       y' <- strengthensN s' y
       pure (x', y')

public export
interface Convert tm where
  convert : {auto c : Ref Ctxt Defs} ->
            {vars : Scope} ->
            Defs -> Env Term vars ->
            tm vars -> tm vars -> Core Bool
  convertInf : {auto c : Ref Ctxt Defs} ->
               {vars : Scope} ->
               Defs -> Env Term vars ->
               tm vars -> tm vars -> Core Bool

  convGen : {auto c : Ref Ctxt Defs} ->
            {vars : _} ->
            Ref QVar Int ->
            Bool -> -- skip forced arguments (must have checked the type
                    -- elsewhere first)
            Defs -> Env Term vars ->
            tm vars -> tm vars -> Core Bool

  convert defs env tm tm'
      = do q <- newRef QVar 0
           convGen q False defs env tm tm'

  convertInf defs env tm tm'
      = do q <- newRef QVar 0
           convGen q True defs env tm tm'

tryUpdate : {vars, vars' : _} ->
            List (Var vars, Var vars') ->
            Term vars -> Maybe (Term vars')
tryUpdate ms (Local fc l idx p)
    = do MkVar p' <- findIdx ms idx
         pure $ Local fc l _ p'
tryUpdate ms (Ref fc nt n) = pure $ Ref fc nt n
tryUpdate ms (Meta fc n i args) = pure $ Meta fc n i !(traverse (tryUpdate ms) args)
tryUpdate ms (Bind fc x b sc)
    = do b' <- tryUpdateB b
         pure $ Bind fc x b' !(tryUpdate (map weakenP ms) sc)
  where
    tryUpdatePi : PiInfo (Term vars) -> Maybe (PiInfo (Term vars'))
    tryUpdatePi Explicit = pure Explicit
    tryUpdatePi Implicit = pure Implicit
    tryUpdatePi AutoImplicit = pure AutoImplicit
    tryUpdatePi (DefImplicit t) = pure $ DefImplicit !(tryUpdate ms t)

    tryUpdateB : Binder (Term vars) -> Maybe (Binder (Term vars'))
    tryUpdateB (Lam fc r p t) = pure $ Lam fc r !(tryUpdatePi p) !(tryUpdate ms t)
    tryUpdateB (Let fc r v t) = pure $ Let fc r !(tryUpdate ms v) !(tryUpdate ms t)
    tryUpdateB (Pi fc r p t) = pure $ Pi fc r !(tryUpdatePi p) !(tryUpdate ms t)
    tryUpdateB _ = Nothing

    weakenP : {n : _} -> (Var vars, Var vars') ->
              (Var (Scope.bind vars n), Var (Scope.bind vars' n))
    weakenP (v, vs) = (weaken v, weaken vs)
tryUpdate ms (App fc f a) = pure $ App fc !(tryUpdate ms f) !(tryUpdate ms a)
tryUpdate ms (As fc s a p) = pure $ As fc s !(tryUpdate ms a) !(tryUpdate ms p)
tryUpdate ms (TDelayed fc r tm) = pure $ TDelayed fc r !(tryUpdate ms tm)
tryUpdate ms (TDelay fc r ty tm) = pure $ TDelay fc r !(tryUpdate ms ty) !(tryUpdate ms tm)
tryUpdate ms (TForce fc r tm) = pure $ TForce fc r !(tryUpdate ms tm)
tryUpdate ms (PrimVal fc c) = pure $ PrimVal fc c
tryUpdate ms (Erased fc a) = Erased fc <$> traverse (tryUpdate ms) a
tryUpdate ms (TType fc u) = pure $ TType fc u

mutual
  allConvNF : {auto c : Ref Ctxt Defs} ->
              {vars : _} ->
              Ref QVar Int -> Bool -> Defs -> Env Term vars ->
              SnocList (NF vars) -> SnocList (NF vars) -> Core Bool
  allConvNF q i defs env [<] [<] = pure True
  allConvNF q i defs env (xs :< x) (ys :< y)
      = do ok <- allConvNF q i defs env xs ys
           if ok then convGen q i defs env x y
                 else pure False
  allConvNF q i defs env _ _ = pure False

  -- return False if anything differs at the head, to quickly find
  -- conversion failures without going deeply into all the arguments.
  -- True means they might still match
  quickConv : SnocList (NF vars) -> SnocList (NF vars) -> Bool
  quickConv [<] [<] = True
  quickConv (xs :< x) (ys :< y) = quickConvArg x y && quickConv xs ys
    where
      quickConvHead : NHead vars -> NHead vars -> Bool
      quickConvHead (NLocal _ _ _) (NLocal _ _ _) = True
      quickConvHead (NRef _ n) (NRef _ n') = n == n'
      quickConvHead (NMeta n _ _) (NMeta n' _ _) = n == n'
      quickConvHead _ _ = False

      quickConvArg : NF vars -> NF vars -> Bool
      quickConvArg (NBind{}) _ = True -- let's not worry about eta here...
      quickConvArg _ (NBind{}) = True
      quickConvArg (NApp _ h _) (NApp _ h' _) = quickConvHead h h'
      quickConvArg (NDCon _ _ t _ _) (NDCon _ _ t' _ _) = t == t'
      quickConvArg (NTCon _ n _ _ _) (NTCon _ n' _ _ _) = n == n'
      quickConvArg (NAs _ _ _ t) (NAs _ _ _ t') = quickConvArg t t'
      quickConvArg (NDelayed _ _ t) (NDelayed _ _ t') = quickConvArg t t'
      quickConvArg (NDelay _ _ _ _) (NDelay _ _ _ _) = True
      quickConvArg (NForce _ _ t _) (NForce _ _ t' _) = quickConvArg t t'
      quickConvArg (NPrimVal _ c) (NPrimVal _ c') = c == c'
      quickConvArg (NType _ _) (NType _ _) = True
      quickConvArg (NErased _ _) _ = True
      quickConvArg _ (NErased _ _) = True
      quickConvArg _ _ = False
  quickConv _ _ = False

  allConv : {auto c : Ref Ctxt Defs} ->
            {vars : _} ->
            Ref QVar Int -> Bool -> Defs -> Env Term vars ->
            SnocList (Closure vars) -> SnocList (Closure vars) -> Core Bool
  allConv q i defs env xs ys
      = do xsnf <- traverse (evalClosure defs) xs
           ysnf <- traverse (evalClosure defs) ys
           if quickConv xsnf ysnf
              then allConvNF q i defs env xsnf ysnf
              else pure False

  -- If the case trees match in structure, get the list of variables which
  -- have to match in the call
  getMatchingVarAlt : {auto c : Ref Ctxt Defs} ->
                      {args, args' : _} ->
                      Defs ->
                      List (Var args, Var args') ->
                      CaseAlt args -> CaseAlt args' ->
                      Core (Maybe (List (Var args, Var args')))
  getMatchingVarAlt defs ms (ConCase n tag cargs t) (ConCase n' tag' cargs' t')
      = if n == n'
           then do let s = mkSizeOf cargs
                   let s' = mkSizeOf cargs'
                   let Just ms' = extend s s' ms
                        | Nothing => pure Nothing
                   Just ms <- getMatchingVars defs ms' t t'
                        | Nothing => pure Nothing
                   -- drop the prefix from cargs/cargs' since they won't
                   -- be in the caller
                   pure (Just (mapMaybe (dropP s s') ms))
           else pure Nothing
    where
      weakenP : {0 c, c' : _} -> {0 args, args' : Scope} ->
                (Var args, Var args') ->
                (Var (args :< c), Var (args' :< c'))
      weakenP (v, vs) = (weaken v, weaken vs)

  getMatchingVarAlt defs ms (ConstCase c t) (ConstCase c' t')
      = if c == c'
           then getMatchingVars defs ms t t'
           else pure Nothing
  getMatchingVarAlt defs ms (DefaultCase t) (DefaultCase t')
      = getMatchingVars defs ms t t'
  getMatchingVarAlt defs _ _ _ = pure Nothing

  getMatchingVarAlts : {auto c : Ref Ctxt Defs} ->
                       {args, args' : _} ->
                       Defs ->
                       List (Var args, Var args') ->
                       List (CaseAlt args) -> List (CaseAlt args') ->
                       Core (Maybe (List (Var args, Var args')))
  getMatchingVarAlts defs ms [] [] = pure (Just ms)
  getMatchingVarAlts defs ms (a :: as) (a' :: as')
      = do Just ms <- getMatchingVarAlt defs ms a a'
                | Nothing => pure Nothing
           getMatchingVarAlts defs ms as as'
  getMatchingVarAlts defs _ _ _ = pure Nothing

  getMatchingVars : {auto c : Ref Ctxt Defs} ->
                    {args, args' : _} ->
                    Defs ->
                    List (Var args, Var args') ->
                    CaseTree args -> CaseTree args' ->
                    Core (Maybe (List (Var args, Var args')))
  getMatchingVars defs ms (Case _ p _ alts) (Case _ p' _ alts')
      = getMatchingVarAlts defs ((MkVar p, MkVar p') :: ms) alts alts'
  getMatchingVars defs ms (STerm i tm) (STerm i' tm')
      = do let Just tm'' = tryUpdate ms tm
               | Nothing => pure Nothing
           if !(convert defs (mkEnv (getLoc tm) args') tm'' tm')
              then pure (Just ms)
              else pure Nothing
  getMatchingVars defs ms (Unmatched _) (Unmatched _) = pure (Just ms)
  getMatchingVars defs ms Impossible Impossible = pure (Just ms)
  getMatchingVars _ _ _ _ = pure Nothing

  chkSameDefs : {auto c : Ref Ctxt Defs} ->
                {vars : _} ->
                Ref QVar Int -> Bool -> Defs -> Env Term vars ->
                Name -> Name ->
                SnocList (Closure vars) -> SnocList (Closure vars) -> Core Bool
  chkSameDefs q i defs env n n' nargs nargs'
     = do Just (PMDef _ args ct rt _) <- lookupDefExact n (gamma defs)
               | _ => pure False
          Just (PMDef _ args' ct' rt' _) <- lookupDefExact n' (gamma defs)
               | _ => pure False

          -- If the two case blocks match in structure, get which variables
          -- correspond. If corresponding variables convert, the two case
          -- blocks convert.
          Just ms <- getMatchingVars defs [] ct ct'
               | Nothing => pure False
          convertMatches ms
     where
       -- We've only got the index into the argument list, and the indices
       -- don't match up, which is annoying. But it'll always be there!
       getArgPos : Nat -> SnocList (Closure vars) -> Maybe (Closure vars)
       getArgPos _ [<] = Nothing
       getArgPos Z (cs :< c) = pure c
       getArgPos (S k) (cs :< c) = getArgPos k cs

       convertMatches : {vs, vs' : _} ->
                        List (Var vs, Var vs') ->
                        Core Bool
       convertMatches [] = pure True
       convertMatches ((MkVar {varIdx = ix} p, MkVar {varIdx = iy} p') :: vs)
          = do let Just varg = getArgPos ix nargs
                   | Nothing => pure False
               let Just varg' = getArgPos iy nargs'
                   | Nothing => pure False
               pure $ !(convGen q i defs env varg varg') &&
                      !(convertMatches vs)

  -- If two names are standing for case blocks, check the blocks originate
  -- from the same place, and have the same scrutinee
  chkConvCaseBlock : {auto c : Ref Ctxt Defs} ->
                     {vars : _} ->
                     FC -> Ref QVar Int -> Bool -> Defs -> Env Term vars ->
                     NHead vars -> SnocList (Closure vars) ->
                     NHead vars -> SnocList (Closure vars) -> Core Bool
  chkConvCaseBlock fc q i defs env (NRef _ n) nargs (NRef _ n') nargs'
      = do NS _ (CaseBlock _ _) <- full (gamma defs) n
              | _ => pure False
           NS _ (CaseBlock _ _) <- full (gamma defs) n'
              | _ => pure False
           False <- chkSameDefs q i defs env n n' nargs nargs'
              | True => pure True
           -- both case operators. Due to the way they're elaborated, two
           -- blocks might arise from the same source but have different
           -- names. So we consider them the same if the scrutinees convert,
           -- and the functions are defined at the same location. This is a
           -- bit of a hack - and relies on the location being stored in the
           -- term accurately - but otherwise it's a quick way to find out!
           Just def <- lookupCtxtExact n (gamma defs)
                | _ => pure False
           Just def' <- lookupCtxtExact n' (gamma defs)
                | _ => pure False
           let PMDef _ _ tree _ _ = definition def
                | _ => pure False
           let PMDef _ _ tree' _ _ = definition def'
                | _ => pure False
           let Just scpos = findArgPos tree
                | Nothing => pure False
           let Just scpos' = findArgPos tree'
                | Nothing => pure False
           let Just sc = getScrutinee ((length nargs) `minus` scpos + 1) nargs
                | Nothing => pure False
           let Just sc' = getScrutinee ((length nargs') `minus` scpos' + 1) nargs'
                | Nothing => pure False
           ignore $ convGen q i defs env sc sc'
           pure (location def == location def')
    where
      -- Need to find the position of the scrutinee to see if they are the
      -- same
      findArgPos : CaseTree as -> Maybe Nat
      findArgPos (Case idx p _ _) = Just idx
      findArgPos _ = Nothing

      getScrutinee : Nat -> SnocList (Closure vs) -> Maybe (Closure vs)
      getScrutinee Z (xs :< x) = Just x
      getScrutinee (S k) (xs :< x) = getScrutinee k xs
      getScrutinee _ _ = Nothing
  chkConvCaseBlock _ _ _ _ _ _ _ _ _ = pure False

  chkConvHead : {auto c : Ref Ctxt Defs} ->
                {vars : _} ->
                Ref QVar Int -> Bool -> Defs -> Env Term vars ->
                NHead vars -> NHead vars -> Core Bool
  chkConvHead q i defs env (NLocal _ idx _) (NLocal _ idx' _) = pure $ idx == idx'
  chkConvHead q i defs env (NRef _ n) (NRef _ n') = pure $ n == n'
  chkConvHead q inf defs env (NMeta n i args) (NMeta n' i' args')
     = if i == i'
          then allConv q inf defs env args args'
          else pure False
  chkConvHead q i defs env _ _ = pure False

  convPiInfo : {auto c : Ref Ctxt Defs} ->
               {vars : _} ->
               Ref QVar Int -> Bool -> Defs -> Env Term vars ->
               PiInfo (Closure vars) -> PiInfo (Closure vars) -> Core Bool
  convPiInfo q i defs env Implicit Implicit = pure True
  convPiInfo q i defs env Explicit Explicit = pure True
  convPiInfo q i defs env AutoImplicit AutoImplicit = pure True
  convPiInfo q i defs env (DefImplicit x) (DefImplicit y) = convGen q i defs env x y
  convPiInfo q i defs env _ _ = pure False

  convBinders : {auto c : Ref Ctxt Defs} ->
                {vars : _} ->
                Ref QVar Int -> Bool -> Defs -> Env Term vars ->
                Binder (Closure vars) -> Binder (Closure vars) -> Core Bool
  convBinders q i defs env bx by
    = if sameBinders bx by && multiplicity bx == multiplicity by
         then allM id [ convPiInfo q i defs env (piInfo bx) (piInfo by)
                      , convGen q i defs env (binderType bx) (binderType by)]
         else pure False
    where
      sameBinders : Binder (Closure vars) -> Binder (Closure vars) -> Bool
      sameBinders (Pi {}) (Pi {}) = True
      sameBinders (Lam {}) (Lam {}) = True
      sameBinders _ _ = False

  export
  Convert NF where
    convGen q i defs env (NBind fc x b sc) (NBind _ x' b' sc')
        = do var <- genName "conv"
             let c = MkClosure defaultOpts LocalEnv.empty env (Ref fc Bound var)
             bok <- convBinders q i defs env b b'
             if bok
                then do bsc <- sc defs c
                        bsc' <- sc' defs c
                        convGen q i defs env bsc bsc'
                else pure False

    convGen q i defs env tmx@(NBind fc x (Lam fc' c ix tx) scx) tmy
        = do empty <- clearDefs defs
             etay <- nf defs env
                        (Bind fc x (Lam fc' c !(traverse (quote empty env) ix) !(quote empty env tx))
                           (App fc (weaken !(quote empty env tmy))
                                (Local fc Nothing _ First)))
             convGen q i defs env tmx etay
    convGen q i defs env tmx tmy@(NBind fc y (Lam fc' c iy ty) scy)
        = do empty <- clearDefs defs
             etax <- nf defs env
                        (Bind fc y (Lam fc' c !(traverse (quote empty env) iy) !(quote empty env ty))
                           (App fc (weaken !(quote empty env tmx))
                                (Local fc Nothing _ First)))
             convGen q i defs env etax tmy

    convGen q inf defs env (NApp fc val args) (NApp _ val' args')
        = if !(chkConvHead q inf defs env val val')
             then case !(getInfPos val) of
                    [] => allConv q inf defs env args1 args2
                    i  => allConv q inf defs env
                                  (dropInf i args1 $ mkSizeOf args1)
                                  (dropInf i args2 $ mkSizeOf args2)

             else chkConvCaseBlock fc q inf defs env val args1 val' args2
        where
          getInfPos : NHead vars -> Core (List Nat)
          getInfPos (NRef _ n)
              = if inf
                   then do Just gdef <- lookupCtxtExact n (gamma defs)
                                | _ => pure []
                           pure (inferrable gdef)
                   else pure []
          getInfPos _ = pure []

          dropInf : List Nat -> (sx : SnocList a) -> SizeOf sx -> SnocList a
          dropInf _ [<] _ = [<]
          dropInf ds (sx :< x) (MkSizeOf (S i) (S p))
              = if i `elem` ds
                   then dropInf ds sx (MkSizeOf i p)
                   else dropInf ds sx (MkSizeOf i p) :< x

          -- Discard file context information irrelevant for conversion checking
          args1 : SnocList (Closure vars)
          args1 = map snd args

          args2 : SnocList (Closure vars)
          args2 = map snd args'

    convGen q i defs env (NDCon _ nm tag _ args) (NDCon _ nm' tag' _ args')
        = if tag == tag'
             then allConv q i defs env (map snd args) (map snd args')
             else pure False
    convGen q i defs env (NTCon _ nm tag _ args) (NTCon _ nm' tag' _ args')
        = if nm == nm'
             then allConv q i defs env (map snd args) (map snd args')
             else pure False
    convGen q i defs env (NAs _ _ _ tm) (NAs _ _ _ tm')
        = convGen q i defs env tm tm'

    convGen q i defs env (NDelayed _ r arg) (NDelayed _ r' arg')
        = if compatible r r'
             then convGen q i defs env arg arg'
             else pure False
    convGen q i defs env (NDelay _ r _ arg) (NDelay _ r' _ arg')
        = if compatible r r'
             then do -- if it's codata, don't reduce the argument or we might
                     -- go for ever, if it's infinite
                     adefs <- case r of
                                   LLazy => pure defs
                                   _ => clearDefs defs
                     convGen q i adefs env arg arg'
             else pure False
    convGen q i defs env (NForce _ r arg args) (NForce _ r' arg' args')
        = if compatible r r'
             then if !(convGen q i defs env arg arg')
                     then allConv q i defs env (map snd args) (map snd args')
                     else pure False
             else pure False

    convGen q i defs env (NPrimVal _ c) (NPrimVal _ c') = pure (c == c')
    convGen q i defs env (NErased _ (Dotted t)) u = convGen q i defs env t u
    convGen q i defs env t (NErased _ (Dotted u)) = convGen q i defs env t u
    convGen q i defs env (NErased _ _) _ = pure True
    convGen q i defs env _ (NErased _ _) = pure True
    convGen q i defs env (NType _ ul) (NType _ ur)
        = -- TODO Cumulativity: Add constraint here
          pure True
    convGen q i defs env x y = pure False

  export
  Convert Term where
    convGen q i defs env x y
        = convGen q i defs env !(nf defs env x) !(nf defs env y)

  export
  Convert Closure where
    convGen q i defs env x y
        = convGen q i defs env !(evalClosure defs x) !(evalClosure defs y)
