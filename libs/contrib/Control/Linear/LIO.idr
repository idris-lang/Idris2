module Control.Linear.LIO

import public Data.So

||| Like `Monad`, but the action and continuation must be run exactly once
||| to ensure that the computation is linear.
public export
interface LinearBind io where
  bindL : (1 _ : io a) -> (1 _ : a -> io b) -> io b

export
LinearBind IO where
  bindL = io_bind

||| Required usage on the result value of a computation
public export
data Usage = None | Linear | Unrestricted

-- Not sure about this - it is a horrible hack, but it makes the notation
-- a bit nicer and consistent with the numbering on binders!
public export 
fromInteger : (x : Integer) -> {auto _ : So (x == 0 || x == 1)} -> Usage
fromInteger 0 = None
fromInteger 1 = Linear
fromInteger x = Unrestricted

||| A wrapper which allows operations to state the multiplicity of the value
||| they return. For example, `L IO {u=1} File` is an IO operation which returns
||| a file that must be used exactly once.
export
data L : (Type -> Type) ->
         {default Unrestricted use : Usage} ->
         Type -> Type where
     MkL : (1 _ : io a) -> L io {use} a

||| Run a linear program with unrestricted return value in the underlying
||| context
export
run : L io a -> io a
run (MkL p) = p

public export
0 ContType : (Type -> Type) -> Usage -> Usage -> Type -> Type -> Type
ContType io None u_k a b = (0 _ : a) -> L io {use=u_k} b
ContType io Linear u_k a b = (1 _ : a) -> L io {use=u_k} b
ContType io Unrestricted u_k a b = a -> L io {use=u_k} b

export %inline
lio_bind : {u_act : _} ->
           LinearBind io =>
           (1 _ : L io {use=u_act} a) ->
           (1 _ : ContType io u_act u_k a b) -> L io {use=u_k} b
lio_bind {u_act = None} (MkL act) k
    = let (>>=) = bindL in
          MkL $ do a' <- act
                   let MkL ka' = k a'
                   ka'
lio_bind {u_act = Linear} (MkL act) k
    = let (>>=) = bindL in
          MkL $ do a' <- act
                   let MkL ka' = k a'
                   ka'
lio_bind {u_act = Unrestricted} (MkL act) k
    = let (>>=) = bindL in
          MkL $ do a' <- act
                   let MkL ka' = k a'
                   ka'

export
Functor io => Functor (L io {use}) where
  map fn (MkL act) = MkL (map fn act)

export
Applicative io => Applicative (L io {use}) where
  pure = MkL . pure
  (<*>) (MkL f) (MkL a) = MkL (f <*> a)

export
(Applicative m, LinearBind m) => Monad (L m) where
  (>>=) = lio_bind

-- prioritise this one for concrete LIO, so we get the most useful
-- linearity annotations.
export %inline
(>>=) : {u_act : _} ->
        LinearBind io =>
        (1 _ : L io {use=u_act} a) ->
        (1 _ : ContType io u_act u_k a b) -> L io {use=u_k} b
(>>=) = lio_bind

export
(LinearBind io, HasIO io) => HasIO (L io) where
  liftIO p = MkL (liftIO p)

public export
LinearIO : (Type -> Type) -> Type
LinearIO io = (LinearBind io, HasIO io)

-- Since the usage won't be known, we need this to be a %defaulthint to allow
-- using arbitrary IO operations at unrestricted multiplicity.
export %defaulthint
unrLIO : LinearBind io => HasIO io => HasIO (L io)
unrLIO = %search
