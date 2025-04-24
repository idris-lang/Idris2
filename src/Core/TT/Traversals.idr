module Core.TT.Traversals

import Core.TT

import Data.DPair
import Data.SortedSet
import Data.Vect
import Libraries.Data.NameMap

%default covering

-- TODO fix future type error
export
onPRefs : Monoid m =>
          (Name      -> m) ->
          (Term vars -> m)
onPRefs f = go neutral where

  go  : m -> Term vars' -> m
  gos : m -> List (Term vars') -> m
  goScope : m -> CaseScope vars' -> m
  goAlt : m -> CaseAlt vars' -> m
  goAlts : m -> List (CaseAlt vars') -> m

  go acc (Local fc isLet idx p) = acc
  go acc (Ref fc x name) = acc <+> f name
  go acc (Meta fc x y xs) = gos acc $ map snd xs
  go acc (Bind fc x b scope) = go (acc <+> concatMap (onPRefs f) b) scope
  go acc (App fc fn _ arg) = go (go acc fn) arg
  go acc (As fc x as pat) = go (go acc as) pat
  go acc (Case fc t c sc scty alts) = goAlts (go (go acc sc) scty) alts
  go acc (TDelayed fc x y) = go acc y
  go acc (TDelay fc x ty arg) = go (go acc ty) arg
  go acc (TForce fc x y) = go acc y
  go acc (PrimVal fc c) = acc
  go acc (PrimOp fc fn args) = gos acc (toList args)
  go acc (Erased fc imp) = acc
  go acc (TType fc u) = acc
  go acc (Unmatched fc _) = acc

  goScope acc (RHS _ tm) = go acc tm
  goScope acc (Arg c x sc) = goScope acc sc

  goAlt acc (ConCase _ n t sc) = goScope acc sc
  goAlt acc (DelayCase _ ty arg tm) = go acc tm
  goAlt acc (ConstCase _ c tm) = go acc tm
  goAlt acc (DefaultCase _ tm) = go acc tm

  gos acc [] = acc
  gos acc (x :: xs) = gos (go acc x) xs

  goAlts acc [] = acc
  goAlts acc (x :: xs) = goAlts (goAlt acc x) xs

export
allGlobals : Term vars -> NameMap ()
allGlobals = onPRefs (\ n => singleton n ())

export
onConstants : Monoid m =>
          (Constant  -> m) ->
          (Term vars -> m)
onConstants f = go neutral where

  go  : m -> Term vars' -> m
  gos : m -> List (Term vars') -> m
  goScope : m -> CaseScope vars' -> m
  goAlt : m -> CaseAlt vars' -> m
  goAlts : m -> List (CaseAlt vars') -> m

  go acc (Local fc isLet idx p) = acc
  go acc (Ref fc x name) = acc
  go acc (Meta fc x y xs) = gos acc $ map snd xs
  go acc (Bind fc x b scope) = go (acc <+> concatMap (onConstants f) b) scope
  go acc (App fc fn _ arg) = go (go acc fn) arg
  go acc (As fc x as pat) = go (go acc as) pat
  go acc (Case fc ty c sc scty alts) = goAlts (go (go acc sc) scty) alts
  go acc (TDelayed fc x y) = go acc y
  go acc (TDelay fc x ty arg) = go (go acc ty) arg
  go acc (TForce fc x y) = go acc y
  go acc (PrimVal fc c) = acc <+> f c
  go acc (PrimOp fc fn args) = gos acc (toList args)
  go acc (Erased fc imp) = acc
  go acc (TType fc u) = acc
  go acc (Unmatched fc _) = acc

  gos acc [] = acc
  gos acc (x :: xs) = gos (go acc x) xs

  goScope acc (RHS _ tm) = go acc tm
  goScope acc (Arg c x sc) = goScope acc sc

  goAlt acc (ConCase _ n t sc) = goScope acc sc
  goAlt acc (DelayCase _ ty arg tm) = go acc tm
  goAlt acc (ConstCase _ c tm) = go acc tm
  goAlt acc (DefaultCase _ tm) = go acc tm

  goAlts acc [] = acc
  goAlts acc (x :: xs) = goAlts (goAlt acc x) xs

export
allConstants : Term vars -> SortedSet Constant
allConstants = onConstants @{MkMonoid @{MkSemigroup union} empty} singleton

export
mapTermM : Monad m =>
           ({vars : _} -> Term vars -> m (Term vars)) ->
           ({vars : _} -> Term vars -> m (Term vars))
mapTermM f t = act t where

  act : {vars : _} -> Term vars -> m (Term vars)
  go  : {vars : _} -> Term vars -> m (Term vars)
  goScope  : {vars : _} -> CaseScope vars -> m (CaseScope vars)
  goAlt  : {vars : _} -> CaseAlt vars -> m (CaseAlt vars)

  act t = f =<< go t

  go t@(Local fc isLet idx p) = pure t
  go t@(Ref fc x name) = pure t
  go t@(Meta fc x y xs) = Meta fc x y <$> traverse @{Compose} act xs
  go t@(Bind fc x b scope) = Bind fc x <$> traverse act b <*> act scope
  go t@(App fc fn c arg) = App fc <$> act fn <*> pure c <*> act arg
  go t@(As fc x as pat) = As fc x <$> act as <*> act pat
  go t@(Case fc ty c sc scty alts)
    = Case fc ty c <$> act sc <*> act scty <*> traverse goAlt alts
  go t@(TDelayed fc x y) = TDelayed fc x <$> act y
  go t@(TDelay fc x ty arg) = TDelay fc x <$> act ty <*> act arg
  go t@(TForce fc x y) = pure t
  go t@(PrimVal fc c) = pure t
  go t@(PrimOp fc fn args) = PrimOp fc fn <$> traverse act args
  go t@(Erased fc imp) = pure t
  go t@(TType fc u) = pure t
  go t@(Unmatched fc _) = pure t

  goScope (RHS fs tm)
      = RHS <$> traverse (\ (n, t) => pure (n, !(act t))) fs <*> act tm
  goScope (Arg c x sc) = Arg c x <$> goScope sc

  goAlt (ConCase fc n t sc) = ConCase fc n t <$> goScope sc
  goAlt (DelayCase fc t a tm) = DelayCase fc t a <$> act tm
  goAlt (ConstCase fc c tm) = ConstCase fc c <$> act tm
  goAlt (DefaultCase fc tm) = DefaultCase fc <$> act tm

export
mapTerm : ({vars : _} -> Term vars -> Term vars) ->
          ({vars : _} -> Term vars -> Term vars)
mapTerm f t = act t where

  act : {vars : _} -> Term vars -> Term vars
  go  : {vars : _} -> Term vars -> Term vars
  goScope  : {vars : _} -> CaseScope vars -> CaseScope vars
  goAlt  : {vars : _} -> CaseAlt vars -> CaseAlt vars

  act t = f (go t)

  go t@(Local fc isLet idx p) = t
  go t@(Ref fc x name) = t
  go t@(Meta fc x y xs) = Meta fc x y (map @{Compose} act xs)
  go t@(Bind fc x b scope) = Bind fc x (map act b) (act scope)
  go t@(App fc fn c arg) = App fc (act fn) c (act arg)
  go t@(As fc x as pat) = As fc x (act as) (act pat)
  go t@(Case fc ty c sc scty alts) = Case fc ty c (act sc) (act scty) (map goAlt alts)
  go t@(TDelayed fc x y) = TDelayed fc x (act y)
  go t@(TDelay fc x ty arg) = TDelay fc x (act ty) (act arg)
  go t@(TForce fc x y) = t
  go t@(PrimVal fc c) = t
  go t@(PrimOp fc fn args) = PrimOp fc fn (map act args)
  go t@(Erased fc imp) = t
  go t@(TType fc u) = t
  go t@(Unmatched fc u) = t

  goScope (RHS fs tm) = RHS (map (\ (n, t) => (n, act t)) fs) (act tm)
  goScope (Arg c x sc) = Arg c x (goScope sc)

  goAlt (ConCase fc n t sc) = ConCase fc n t (goScope sc)
  goAlt (DelayCase fc t a tm) = DelayCase fc t a (act tm)
  goAlt (ConstCase fc c tm) = ConstCase fc c (act tm)
  goAlt (DefaultCase fc tm) = DefaultCase fc (act tm)
