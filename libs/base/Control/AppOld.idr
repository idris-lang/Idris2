module Control.App

import Data.List
import Data.IORef

public export
data Effect : Type where
     St : Type -> Effect
     Exc : Type -> Effect
     Sys : Effect

public export
data HasEff : Effect -> List Effect -> Type where
     Here : HasEff e (e :: es)
     There : HasEff e es -> HasEff e (e' :: es)

public export
0 Has : List (a -> Type) -> a -> Type
Has [] es = ()
Has [e] es = e es
Has (e :: es') es = (e es, Has es' es)

export
data Env : List Effect -> Type where
     None : Env []
     Ref : IORef t -> Env es -> Env (St t :: es)
     SkipE : Env es -> Env (Exc t :: es)
     SkipP : Env es -> Env (Sys :: es)

getState : Env es -> (p : HasEff (St t) es) -> IORef t
getState (Ref r env) Here = r
getState (Ref r env) (There p) = getState env p
getState (SkipE env) (There p) = getState env p
getState (SkipP env) (There p) = getState env p

public export
data Path : Type where
     [noHints]
     MayThrow : Path
     NoThrow : Path

%hint public export
dpath : Path
dpath = MayThrow

data OneOf : List Type -> Path -> Type where
     First : e -> OneOf (e :: es) MayThrow
     Later : OneOf es MayThrow -> OneOf (e :: es) MayThrow

updateP : OneOf es p -> OneOf es p'
updateP {p=MayThrow} {p'=MayThrow} x = x

Uninhabited (OneOf [] p) where
  uninhabited (First x) impossible
  uninhabited (Later x) impossible

Uninhabited (OneOf es NoThrow) where
  uninhabited (First x) impossible
  uninhabited (Later x) impossible

public export
0 excTy : List Effect -> List Type
excTy [] = []
excTy (St t :: es) = excTy es
excTy (Exc e :: es) = e :: excTy es
excTy (Sys :: es) = excTy es

0 execTy : Path -> List Effect -> Type -> Type
execTy p es ty = Either (OneOf (excTy es) p) ty

export
data App : (l : Path) => (es : List Effect) -> Type -> Type where
     MkApp : (1 prog : Env e -> IO (execTy l e t)) -> App {l} e t

pureApp : a -> App {l} e a
pureApp x = MkApp (\env => pure (Right x))

public export
data SafeBind : Path -> (l' : Path) -> Type where
     [search l']
     SafeSame : SafeBind l l
     SafeToThrow : SafeBind NoThrow MayThrow

bindApp : SafeBind l l' =>
          App {l} e a -> (a -> App {l=l'} e b) -> App {l=l'} e b
bindApp (MkApp prog) k
    = MkApp $ \env =>
              do Right res <- prog env
                       | Left err => pure (Left (updateP err))
                 let MkApp ka = k res
                 ka env

absurdWith : (1 x : a) -> OneOf e NoThrow -> any
absurdWith x (First p) impossible

export
bindL : App {l=NoThrow} e a -> (1 k : a -> App {l} e b) -> App {l} e b
bindL (MkApp prog) k
    = MkApp $ \env =>
              io_bind (prog env) $ \r =>
                   case r of
                        Left err => absurdWith k err
                        Right res =>
                              let MkApp ka = k res in ka env

export
lift : App e t -> App (eff :: e) t
lift (MkApp p)
    = MkApp (\env =>
          case env of
               Ref r env' => p env'
               SkipP env' => p env'
               SkipE env' =>
                  do res <- p env'
                     case res of
                          Left err => pure (Left (Later err))
                          Right ok => pure (Right ok))

export
Functor (App {l} es) where
  map f ap = bindApp ap $ \ap' => pureApp (f ap')

export
Applicative (App {l} es) where
  pure = pureApp
  (<*>) f a = bindApp f $ \f' =>
              bindApp a $ \a' => pure (f' a')

export
Monad (App es) where
  (>>=) = bindApp -- won't get used, but handy to have the instance

export
(>>=) : SafeBind l l' =>
        App {l} e a -> (k : a -> App {l=l'} e b) -> App {l=l'} e b
(>>=) = bindApp

export
new : a -> App {l} (St a :: es) t -> App {l} es t
new val (MkApp prog)
    = MkApp $ \env =>
          do ref <- newIORef val
             prog (Ref ref env)

public export
interface State t es where
  get : App {l} es t
  put : t -> App {l} es ()

export
HasEff (St t) es => State t es where
  get
      = MkApp $ \env =>
            do let ref = getState env %search
               val <- readIORef ref
               pure (Right val)
  put val
      = MkApp $ \env =>
            do let ref = getState env %search
               writeIORef ref val
               pure (Right ())

public export
interface Exception e es where
  throw : e -> App es a
  catch : App es a -> (err : e -> App es a) -> App es a

findException : Env es -> HasEff (Exc e) es -> e -> OneOf (excTy es) MayThrow
findException (SkipE env) Here err = First err
findException (Ref r env) (There p) err = findException env p err
findException (SkipE env) (There p) err = Later $ findException env p err
findException (SkipP env) (There p) err = findException env p err

findError : Env es -> HasEff (Exc e) es -> OneOf (excTy es) MayThrow -> Maybe e
findError (SkipE env) Here (First err) = Just err
findError (SkipE env) Here (Later p) = Nothing -- wrong exception
findError (SkipE env) (There p) (First err) = Nothing -- wrong exception
findError (SkipE env) (There p) (Later q) = findError env p q
findError (Ref r env) (There p) err = findError env p err
findError (SkipP env) (There p) err = findError env p err

export
HasEff (Exc e) es => Exception e es where
  throw err
      = MkApp $ \env =>
           pure (Left (findException env %search err))
  catch (MkApp prog) handler
      = MkApp $ \env =>
           do res <- prog env
              case res of
                   Left err =>
                        case findError env %search err of
                             Nothing => pure (Left err)
                             Just err' =>
                                  let MkApp e' = handler err' in
                                      e' env
                   Right ok => pure (Right ok)

export
handle : App (Exc err :: e) a ->
         (onok : a -> App e b) ->
         (onerr : err -> App e b) -> App e b
handle (MkApp prog) onok onerr
    = MkApp $ \env =>
          do res <- prog (SkipE env)
             case res of
                  Left (First err) =>
                        let MkApp err' = onerr err in
                            err' env
                  Left (Later p) =>
                        -- different exception, so rethrow
                        pure (Left p)
                  Right ok =>
                        let MkApp ok' = onok ok in
                            ok' env

public export
interface PrimIO es where
  primIO : IO a -> App {l} es a
  -- Copies the environment, to make sure states are local to threads
  fork : App es () -> App {l} es ()

copyEnv : Env es -> IO (Env es)
copyEnv None = pure None
copyEnv (Ref t env)
    = do val <- readIORef t
         t' <- newIORef val
         env' <- copyEnv env
         pure (Ref t' env')
copyEnv (SkipE env)
    = do env' <- copyEnv env
         pure (SkipE env')
copyEnv (SkipP env)
    = do env' <- copyEnv env
         pure (SkipP env')

export
HasEff Sys es => PrimIO es where
  primIO io
      = MkApp $ \env =>
            do res <- io
               pure (Right res)
  fork (MkApp p)
      = MkApp $ \env =>
            do fork (do env' <- copyEnv env
                        p env'
                        pure ())
               pure (Right ())

public export
Init : List Effect
Init = [Sys]

export
run : App Init a -> IO a
run (MkApp prog)
    = do Right res <- prog (SkipP None)
               | Left err => absurd err
         pure res

infix 5 @@

public export
data Res : (a : Type) -> (a -> Type) -> Type where
     (@@) : (val : a) -> (1 r : t val) -> Res a t
