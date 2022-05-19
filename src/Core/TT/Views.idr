module Core.TT.Views

import Core.Env
import Core.TT

||| Go under n Pis (if n < 0 then go under as many as possible)
export
underPis : (n : Int) -> Env Term vars -> Term vars ->
           (bnds : SnocList Name ** (Env Term (bnds <>> vars), Term (bnds <>> vars)))
underPis 0 env t = ([<] ** (env, t))
underPis n env (Bind fc x bd@(Pi{}) scope) =
  let (bnds ** (env', scope')) := underPis (n - 1) (bd :: env) scope in
  (bnds :< x ** (env', scope'))
underPis n env (Bind fc x bd@(PLet fc1 y val ty) scope) = underPis n env (subst val scope)
underPis n env t = ([<] ** (env, t))
