module TTImp.Interactive.MakeLemma

import Core.Context
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.TT

import Idris.Syntax

import TTImp.Unelab
import TTImp.TTImp
import TTImp.TTImp.Functor
import TTImp.Utils

import Data.List
import Data.SnocList

%default covering

used : RigCount -> Bool
used = not . isErased

hiddenName : Name -> Bool
hiddenName (MN "_" _) = True
hiddenName _ = False

-- True if the variable appears guarded by a constructor in the term
bindable : Nat -> Term vars -> Bool
bindable p tm
    = case getFnArgs tm of
           (Ref _ (TyCon _ _) n, args) => any (bindable p) args
           (Ref _ (DataCon _ _) _, args) => any (bindable p) args
           (TDelayed _ _ t, args) => any (bindable p) (t :: args)
           (TDelay _ _ _ t, args) => any (bindable p) (t :: args)
           (TForce _ _ t, args) => any (bindable p) (t :: args)
           (Local _ _ p' _, []) => p == p'
           _ => False

bindableArg : Nat -> Term vars -> Bool
bindableArg p (Bind _ _ (Pi _ _ _ ty) sc)
   = bindable p ty || bindableArg (1 + p) sc
bindableArg p _ = False

getArgs : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          Env Term vars -> Nat -> Term vars ->
          Core (List (Name, Maybe Name, PiInfo RawImp, RigCount, RawImp), RawImp)
getArgs {vars} env (S k) (Bind _ x b@(Pi _ c _ ty) sc)
    = do defs <- get Ctxt
         ty' <- map (map rawName) $ unelab env !(normalise defs env ty)
         let x' = UN $ Basic !(uniqueBasicName defs (toList $ map nameRoot vars) (nameRoot x))
         (sc', ty) <- getArgs (b :: env) k (compat {n = x'} sc)
         -- Don't need to use the name if it's not used in the scope type
         let mn = if c == top
                       then case shrink sc (Drop Refl) of
                                    Nothing => Just x'
                                    _ => Nothing
                       else Just x'
         let p' = if used c && not (bindableArg 0 sc) && not (hiddenName x)
                     then Explicit
                     else Implicit
         pure ((x, mn, p', c, ty') :: sc', ty)
getArgs env k ty
      = do defs <- get Ctxt
           ty' <- map (map rawName) $ unelab env !(normalise defs env ty)
           pure ([], ty')

mkType : FC -> List (Name, Maybe Name, PiInfo RawImp, RigCount, RawImp) ->
         RawImp -> RawImp
mkType loc [] ret = ret
mkType loc ((_, n, p, c, ty) :: rest) ret
    = IPi loc c p n ty (mkType loc rest ret)

mkApp : FC -> Name ->
        List (Name, Maybe Name, PiInfo RawImp, RigCount, RawImp) -> RawImp
mkApp loc n args
    = apply (IVar loc n) (mapMaybe getArg args)
  where
    getArg : (Name, Maybe Name, PiInfo RawImp, RigCount, RawImp) ->
             Maybe RawImp
    getArg (x, _, Explicit, _, _) = Just (IVar loc x)
    getArg _ = Nothing

-- Return a top level type for the lemma, and an expression which applies
-- the lemma to solve a hole with 'locs' arguments
export
makeLemma : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            FC -> Name -> Nat -> ClosedTerm ->
            Core (RawImp, RawImp)
makeLemma loc n nlocs ty
    = do defs <- get Ctxt
         (args, ret) <- getArgs Env.empty nlocs !(normalise defs Env.empty ty)
         pure (mkType loc args ret, mkApp loc n args)
