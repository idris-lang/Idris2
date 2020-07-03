import Data.Vect

data Ty = TyInt | TyBool | TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt       = Integer
interpTy TyBool      = Bool
interpTy (TyFun a t) = interpTy a -> interpTy t

data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
    Stop : HasType FZ (t :: ctxt) t
    Pop  : HasType k ctxt t -> HasType (FS k) (u :: ctxt) t

data Expr : Vect n Ty -> Ty -> Type where
    Var : HasType i ctxt t -> Expr ctxt t
    Val : (x : Integer) -> Expr ctxt TyInt
    Lam : Expr (a :: ctxt) t -> Expr ctxt (TyFun a t)
    App : Expr ctxt (TyFun a t) -> Expr ctxt a -> Expr ctxt t
    Op  : (interpTy a -> interpTy b -> interpTy c) ->
          Expr ctxt a -> Expr ctxt b -> Expr ctxt c
    If  : Expr ctxt TyBool ->
          Lazy (Expr ctxt a) ->
          Lazy (Expr ctxt a) -> Expr ctxt a

data Env : Vect n Ty -> Type where
    Nil  : Env Nil
    (::) : interpTy a -> Env ctxt -> Env (a :: ctxt)

lookup : HasType i ctxt t -> Env ctxt -> interpTy t
lookup Stop    (x :: xs) = x
lookup (Pop k) (x :: xs) = lookup k xs

interp : Env ctxt -> Expr ctxt t -> interpTy t
interp env (Var i)     = lookup i env
interp env (Val x)     = x
interp env (Lam sc)    = \x => interp (x :: env) sc
interp env (App f s)   = interp env f (interp env s)
interp env (Op op x y) = op (interp env x) (interp env y)
interp env (If x t e)  = if interp env x then interp env t
                                         else interp env e

add : Expr ctxt (TyFun TyInt (TyFun TyInt TyInt))
add = Lam (Lam (Op (+) (Var Stop) (Var (Pop Stop))))

fact : Expr ctxt (TyFun TyInt TyInt)
fact = Lam (If (Op (==) (Var Stop) (Val 0))
               (Val 1)
               (Op (*) (App fact (Op (-) (Var Stop) (Val 1)))
                       (Var Stop)))

main : IO ()
main = do putStr "Enter a number: "
          x <- getLine
          printLn (interp [] fact (cast x))



