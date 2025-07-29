module Core.TT.Traversals

import Core.TT
import Core.Ord

import Data.DPair
import Data.SnocList
import Libraries.Data.NameMap
import Libraries.Data.SortedSet

%default covering

-- TODO fix future type error
export
onPRefs : Monoid m =>
          (Name      -> m) ->
          (Term vars -> m)
onPRefs f = go neutral where

  go  : m -> Term vars' -> m
  gos : m -> List (Term vars') -> m

  go acc (Local fc isLet idx p) = acc
  go acc (Ref fc x name) = acc <+> f name
  go acc (Meta fc x y xs) = gos acc xs
  go acc (Bind fc x b scope) = go (acc <+> concatMap (onPRefs f) b) scope
  go acc (App fc fn arg) = go (go acc fn) arg
  go acc (As fc x as pat) = go (go acc as) pat
  go acc (TDelayed fc x y) = go acc y
  go acc (TDelay fc x ty arg) = go (go acc ty) arg
  go acc (TForce fc x y) = go acc y
  go acc (PrimVal fc c) = acc
  go acc (Erased fc imp) = acc
  go acc (TType fc u) = acc

  gos acc [] = acc
  gos acc (x :: xs) = gos (go acc x) xs

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

  go acc (Local fc isLet idx p) = acc
  go acc (Ref fc x name) = acc
  go acc (Meta fc x y xs) = gos acc xs
  go acc (Bind fc x b scope) = go (acc <+> concatMap (onConstants f) b) scope
  go acc (App fc fn arg) = go (go acc fn) arg
  go acc (As fc x as pat) = go (go acc as) pat
  go acc (TDelayed fc x y) = go acc y
  go acc (TDelay fc x ty arg) = go (go acc ty) arg
  go acc (TForce fc x y) = go acc y
  go acc (PrimVal fc c) = acc <+> f c
  go acc (Erased fc imp) = acc
  go acc (TType fc u) = acc

  gos acc [] = acc
  gos acc (x :: xs) = gos (go acc x) xs

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

  act t = f =<< go t

  go t@(Local fc isLet idx p) = pure t
  go t@(Ref fc x name) = pure t
  go t@(Meta fc x y xs) = Meta fc x y <$> traverse act xs
  go t@(Bind fc x b scope) = Bind fc x <$> traverse act b <*> act scope
  go t@(App fc fn arg) = App fc <$> act fn <*> act arg
  go t@(As fc x as pat) = As fc x <$> act as <*> act pat
  go t@(TDelayed fc x y) = TDelayed fc x <$> act y
  go t@(TDelay fc x ty arg) = TDelay fc x <$> act ty <*> act arg
  go t@(TForce fc x y) = pure t
  go t@(PrimVal fc c) = pure t
  go t@(Erased fc imp) = pure t
  go t@(TType fc u) = pure t

export
mapTerm : ({vars : _} -> Term vars -> Term vars) ->
          ({vars : _} -> Term vars -> Term vars)
mapTerm f t = act t where

  act : {vars : _} -> Term vars -> Term vars
  go  : {vars : _} -> Term vars -> Term vars

  act t = f (go t)

  go t@(Local fc isLet idx p) = t
  go t@(Ref fc x name) = t
  go t@(Meta fc x y xs) = Meta fc x y (map act xs)
  go t@(Bind fc x b scope) = Bind fc x (map act b) (act scope)
  go t@(App fc fn arg) = App fc (act fn) (act arg)
  go t@(As fc x as pat) = As fc x (act as) (act pat)
  go t@(TDelayed fc x y) = TDelayed fc x (act y)
  go t@(TDelay fc x ty arg) = TDelay fc x (act ty) (act arg)
  go t@(TForce fc x y) = t
  go t@(PrimVal fc c) = t
  go t@(Erased fc imp) = t
  go t@(TType fc u) = t
