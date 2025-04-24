module Core.Evaluate.Expand

import Core.Context
import Core.Env
import Core.Context.Log
import Core.Evaluate.Value
import Core.Primitives
import Core.Evaluate.Quote

import Data.Vect
import Data.SnocList
import Libraries.Data.WithDefault
import Libraries.Data.SnocList.LengthMatch

data ExpandMode
  = OnlyVisible -- expand names to full names with namespaces to respect their visilibity
  | Cases -- look into top level cases
  | Full -- reduce as much as possible regardless visibility and cases

Show ExpandMode where
  show OnlyVisible = "OnlyVisible"
  show Cases = "Cases"
  show Full = "Full"

Eq ExpandMode where
  (==) OnlyVisible OnlyVisible = True
  (==) Cases Cases = True
  (==) Full Full = True
  (==) _ _ = False

Ord ExpandMode where
  compare OnlyVisible OnlyVisible = EQ
  compare OnlyVisible _ = LT
  compare _ OnlyVisible = GT
  compare Cases Cases = EQ
  compare Cases Full = LT
  compare Full Cases = GT
  compare Full Full = EQ

-- If a value is an App or Meta node, then it might be reducible. Expand it
-- just enough that we have the right top level node.
-- Don't expand Apps to a blocked top level cases, unless 'cases' is set.
-- The 'believe_me' are there to save us deconstructing and reconstructing
-- just to change a compile-time only index
expand' : {auto c : Ref Ctxt Defs} ->
          {vars: _} ->
          ExpandMode -> Value f vars -> Core (NF vars)
expand' mode v@(VApp fc nt n sp val)
    = do vis <- getVisibilityWeaked fc n
         m_mult <- getMultiplicityWeaked fc n
         full_name <- toFullNames n
         defs <- get Ctxt
         let ns = currentNS defs :: nestedNS defs
         logC "eval.def.stuck" 50 $ pure "expand App \{show mode} ns: \{show ns}, n: \{show n}, vis: \{show $ collapseDefault vis}, mult: \{show m_mult}, full_name: \{show full_name}"
         if mode > Cases || reducibleInAny ns (if mode < Cases then full_name else n) (collapseDefault vis)
            -- If we are in Cases we are still needed to confirm that a name can be reduced.
            -- If a name has no namespace (i.e. Resolved _) it will be reduced
            then do
               Just val' <- logDepth val
                    | Nothing => pure (believe_me v)
               logC "eval.def.stuck" 50 $ do val' <- toFullNames val'
                                             pure "Reduced \{show full_name} to \{show val'}"
               if mode >= Cases
                  then expand' mode val'
                  else if !(blockedApp val')
                          then pure (believe_me v)
                          else expand' mode val'
            else pure (believe_me v)
  where
    blockedApp : forall f . Value f vars -> Core Bool
    blockedApp (VBind fc _ (Lam {}) sc)
        = blockedApp !(sc $ pure $ VErased fc Placeholder)
    blockedApp (VCase _ PatMatch _ _ _ _) = pure True
    blockedApp (VPrimOp{}) = pure True
    blockedApp _ = pure False

expand' mode@Full v@(VCase fc t r sc ty alts)
    = do sc' <- logDepth $ expand' mode sc
         logC "eval.def.stuck" 50 $ pure "expand try VCase \{show t} \{show !(toFullNames sc)} (\{show !(toFullNames sc')}) alts: \{show !(toFullNames alts)}"
         Just res <- tryAlts sc' alts
              | Nothing =>
                do logC "eval.def.stuck" 50 $ pure "expand failed VCase \{show t} \{show !(toFullNames sc)} (\{show !(toFullNames sc')}) alts: \{show !(toFullNames alts)}"
                   pure $ VCase fc t r sc' ty alts
         logC "eval.def.stuck" 50 $ pure "expand \{show !(toFullNames v)} to \{show !(toFullNames res)}"
         expand' mode res
  where
    caseScope' : (vs : SnocList (Core (Glued vars))) ->
                 (0 _ : LengthMatch vs args) ->
                 VCaseScope args vars ->
                 Core (Glued vars)
    caseScope' [<] LinMatch scope
      = do logC "eval.def.stuck" 50 $ pure "Begin Expand VCaseScope"
           pure $ snd !scope
    caseScope' (vars :< v) (SnocMatch m) scope
      = do logC "eval.def.stuck" 50 $ pure "Put arg to Expand VCaseScope"
           caseScope' vars m (scope v)

    caseScope : SnocList (Core (Glued vars)) ->
                (args : SnocList (RigCount, Name)) ->
                VCaseScope args vars ->
                Core (Glued vars)
    caseScope vs as scope
      = case checkLengthMatch vs as of
             Just m => caseScope' vs m scope
             Nothing => throw (GenericMsg fc "Stuck to expand VCaseScope: \{show vars}")

    tryAlt : NF vars -> VCaseAlt vars -> Core (Maybe (Glued vars))
    tryAlt _ (VDefaultCase _ rhs) = pure $ Just rhs
    tryAlt (VDCon _ _ t a sp) (VConCase _ _ t' args scoped) =
      if t == t' then do
          pure $ Just !(caseScope (map value sp) args scoped)
        else pure Nothing
    tryAlt (VTCon _ n a sp) (VConCase _ n' _ args scoped) =
      if n == n' then do
          pure $ Just !(caseScope (map value sp) args scoped)
        else pure Nothing
    tryAlt (VDelay _ _ ty arg) (VDelayCase _ ty' arg' rhs) =
        pure $ Just !(caseScope [<pure ty, pure arg] [<(top, ty'), (erased, arg')] rhs)
    tryAlt (VPrimVal _ c) (VConstCase _ c' rhs) =
      if c == c' then pure $ Just rhs
        else pure Nothing
    tryAlt (VErased _ (Dotted v)) alt = tryAlt v alt
    tryAlt _ _ = pure Nothing

    tryAlts : NF vars -> List (VCaseAlt vars) -> Core (Maybe (Glued vars))
    tryAlts sc (a :: alts)
      = case !(tryAlt sc a) of
             Nothing => tryAlts sc alts
             Just res => pure $ Just res
    tryAlts sc [] = pure Nothing

expand' mode@Full (VPrimOp fc op args)
    = do args' <- traverseVect (expand' mode) args
         case getOp op args' of
           Just res => do logC "eval.def.stuck" 50 $ pure "Reduced full VPrimOp op: \{show op} to \{show !(toFullNames res)}"
                          pure res
           Nothing => do logC "eval.def.stuck" 50 $ pure "Reduced only args VPrimOp op: \{show op} \{show $ !(traverse toFullNames $ toList args')}"
                         pure $ VPrimOp fc op args
expand' mode (VErased fc (Dotted t))
    = do t' <- expand' mode t
         pure (VErased fc (Dotted t'))
expand' mode v@(VMeta fc n i args sp val)
    = do logC "eval.def.stuck" 50 $ pure "expand Meta n: \{show n}"
         Just val' <- logDepth val
              | Nothing => pure (believe_me v)
         logC "eval.def.stuck" 50 $ do n' <- toFullNames n
                                       val' <- toFullNames val'
                                       pure "Reduced \{show n'} to \{show val'}"
         expand' mode val'
expand' mode val = pure (believe_me val)

logNF : {vars : _} ->
        {auto c : Ref Ctxt Defs} ->
        LogTopic -> Nat -> Lazy String -> Value f vars -> Core ()
logNF s n msg tmnf
    = when !(logging s n) $
        do defs <- get Ctxt
           tm <- logQuiet $ quote (mkEnv emptyFC _) tmnf
           tm' <- toFullNames tm
           depth <- getDepth
           logString depth s.topic n (msg ++ ": " ++ show tm')

export
expand : {auto c : Ref Ctxt Defs} ->
         {vars: _} ->
         Value f vars -> Core (NF vars)
expand v = do
  logNF "eval.def.stuck" 50 "Begin Expand OnlyVisible for" v
  logDepth $ expand' OnlyVisible v

export
expandCases : {auto c : Ref Ctxt Defs} ->
             {vars: _} ->
             Value f vars -> Core (NF vars)
expandCases v = do
  logNF "eval.def.stuck" 50 "Begin Expand Cases for" v
  logDepth $ expand' Cases v

export
expandFull : {auto c : Ref Ctxt Defs} ->
             {vars: _} ->
             Value f vars -> Core (NF vars)
expandFull v = do
  logNF "eval.def.stuck" 50 "Begin Expand Full for" v
  logDepth $ expand' Full v

export
spineVal : {auto c : Ref Ctxt Defs} ->
           {vars: _} ->
           SpineEntry vars -> Core (NF vars)
spineVal e = expand !(value e)

export
spineValFull : {auto c : Ref Ctxt Defs} ->
           {vars: _} ->
           SpineEntry vars -> Core (NF vars)
spineValFull e = expandFull !(value e)
