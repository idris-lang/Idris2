module Core.TT.Views

import Core.Env
import Core.TT

export
underPis : Env Term vars -> Term vars -> (bnds : SnocList Name ** (Env Term (bnds <>> vars), Term (bnds <>> vars)))
underPis env (Bind fc x bd@(Pi{}) scope) =
  let (bnds ** (env', scope')) := underPis (bd :: env) scope in
  (bnds :< x ** (env', scope'))
underPis env (Bind fc x bd@(PLet fc1 y val ty) scope) = underPis env (subst val scope)
underPis env t = ([<] ** (env, t))
