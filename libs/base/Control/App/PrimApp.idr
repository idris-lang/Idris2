module Control.App.PrimApp

import Data.List
import Data.IORef

public export
data PEffect : Type where
     St : Type -> PEffect
     Exc : Type -> PEffect
     Sys : PEffect

public export
data HasPEff : PEffect -> List PEffect -> Type where
     Here : HasPEff e (e :: es)
     There : HasPEff e es -> HasPEff e (e' :: es)

public export
data NotException : PEffect -> Type where
     StNotE : NotException (St t)
     SysNotE : NotException Sys

public export
data NotState : PEffect -> Type where
     ExcNotS : NotState (Exc t)
     SysNotS : NotState Sys

public export
data Linear : List PEffect -> Type where
     EmptyLin : Linear []
     RestLin : NotException e => Linear es -> Linear (e :: es)

public export
data Stateless : List PEffect -> Type where
     EmptySt : Stateless []
     RestSt : NotState e => Stateless es -> Stateless (e :: es)

export
data Env : List PEffect -> Type where
     None : Env []
     Ref : IORef t -> Env es -> Env (St t :: es)
     SkipE : Env es -> Env (Exc t :: es)
     SkipP : Env es -> Env (Sys :: es)

getState : Env es -> (p : HasPEff (St t) es) -> IORef t
getState (Ref r env) Here = r
getState (Ref r env) (There p) = getState env p
getState (SkipE env) (There p) = getState env p
getState (SkipP env) (There p) = getState env p

public export
0 execTy : List PEffect -> Type -> Type
execTy [] ty = ty
execTy (St t :: es) ty = execTy es ty
execTy (Exc e :: es) ty = Either e (execTy es ty)
execTy (Sys :: es) ty = execTy es ty

public export
data PApp : List PEffect -> Type -> Type where
     Pure : (x : a) -> PApp es a
     Bind : PApp es a -> (a -> PApp es b) -> PApp es b
     BindL : Linear es =>
             (1 act : PApp es a) ->
             (1 k : a -> PApp es b) -> PApp es b

     New : a -> PApp (St a :: es) t -> PApp es t
     Get : HasPEff (St t) es => PApp es t
     Put : HasPEff (St t) es => t -> PApp es ()

     Throw : HasPEff (Exc e) es => e -> PApp es a
     Catch : HasPEff (Exc e) es =>
             PApp es a ->
             (err : e -> PApp es a) -> PApp es a
     Handle : PApp (Exc e :: es) a ->
              (ok : a -> PApp es b) ->
              (err : e -> PApp es b) -> PApp es b

     GetEnv : PApp es (Env es)
     Fork : HasPEff Sys es => PApp es () -> PApp es ()
     Prim : HasPEff Sys es => PrimIO a -> PApp es a

export
Functor (PApp es) where
  map f ap = Bind ap $ \ap' => Pure (f ap')

export
Applicative (PApp es) where
  pure = Pure
  (<*>) f a
      = Bind f $ \f' =>
        Bind a $ \a' => pure (f' a')

export
Monad (PApp es) where
  (>>=) = Bind

throwIn : Env es -> HasPEff (Exc e) es -> e ->
          IO (execTy (es ++ rest) a)
throwIn (SkipE es) Here e = pure (Left e)
throwIn (Ref r es) (There p) e = throwIn es p e
throwIn (SkipE es) (There p) e
    = do res <- throwIn es p e
         pure (Right res)
throwIn (SkipP es) (There p) e = throwIn es p e

findRes : Env es -> HasPEff (Exc e) es -> execTy es a -> Maybe e
findRes (SkipE env) (There p) (Left _) = Nothing -- wrong exception
findRes (SkipE env) (There p) (Right r) = findRes env p r
findRes (Ref r env) (There p) t = findRes env p t
findRes (SkipP env) (There p) t = findRes env p t
findRes None _ _ = Nothing
findRes _ Here (Left ex) = Just ex
findRes _ Here _ = Nothing

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

clearEnv : Env es -> IO (execTy es ())
clearEnv None = pure ()
clearEnv (Ref t env) = clearEnv env
clearEnv (SkipE env)
    = do e' <- clearEnv env
         pure (Right e')
clearEnv (SkipP env) = clearEnv env

exec : Env es -> PApp es t -> (t -> IO (execTy es a)) -> IO (execTy es a)
exec env (Pure val) k = k val
exec env (Bind act next) k
    = exec env act (\res => exec env (next res) k)
exec env (BindL act next) k
    = exec env act (\res => exec env (next res) k)
exec env (New val prog) k
    = do r <- newIORef val
         exec (Ref r env) prog k
exec env (Get @{p}) k
    = do let ref = getState env p
         val <- readIORef ref
         k val
exec env (Put @{p} val) k
    = do let ref = getState env p
         writeIORef ref val
         k ()
exec env (Throw @{p} e) k
    = rewrite sym (appendNilRightNeutral es) in
        throwIn env p e {rest = []}
exec env (Handle prog ok err) k
    = do res <- exec (SkipE env) prog
                     (\res => do res' <- exec env (ok res) k
                                 pure (Right res'))
         case res of
              Left ex => exec env (err ex) k
              Right ok => pure ok
exec env (Catch @{p} prog err) k
    = do res <- exec env prog k
         case findRes env p res of
              Just ex => exec env (err ex) k
              Nothing => pure res
exec env GetEnv k = k env
exec env (Fork proc) k
    = do fork (do env' <- copyEnv env
                  exec env proc (\u => clearEnv env)
                  pure ())
         k ()
exec env (Prim io) k
    = do op <- primIO io
         k op
export
run : PApp [Sys] a -> IO a
run prog = exec (SkipP None) prog pure
