
module Lambda

import NoRegression

%default total

data Ty = TyFunc Ty Ty | TyNat

data Context = Empty | Extend Context Ty

data Contains : Context -> Ty -> Type where
  Here : Contains (Extend g ty) ty
  There : (rest :  Contains g ty)
       -> Contains (Extend g not_ty) ty

data Term : Context -> Ty -> Type where
  Var : (idx : Contains g ty)
     -> Term g ty

  Func : (body : Term (Extend g tyA) tyB)
      -> Term g (TyFunc tyA tyB)

  App : (func : Term g (TyFunc tyA tyB))
     -> (var  : Term g tyA)
     -> Term g tyB

  Zero : Term g TyNat

  Next : (inner : Term g TyNat)
      -> Term g TyNat

  Case : (scrutinee : Term g TyNat)
      -> (zero : Term g tyA)
      -> (next : Term (Extend g TyNat) tyA)
      -> Term g tyA

  Plus : Term g TyNat
      -> Term g TyNat
      -> Term g TyNat

  Rec : (body : Term (Extend g tyA) tyA)
    -> Term g tyA

term : Term Empty
            (TyFunc TyNat -- (Var Here) -
                    (TyFunc TyNat -- (Var (There Here)) -
                            (TyFunc TyNat -- (Var (There (There Here))) -
                                    (TyFunc TyNat -- (Var (There (There (There Here)))) -
                                           (TyFunc TyNat -- (Var (There (There (There (There Here))))) -
                                                   (TyFunc TyNat -- (Var (There (There (There (There (There Here)))))) -
                                                           (TyFunc TyNat -- (Var (There (There (There (There (There (There Here)))))))
                                                                   TyNat
                                                                   )
                                                                   )
                                                                   )
                                                                   )
                                                                   )
                                                                   )
                                                                   )
term =
  Func
      (Func
           (Func
                (Func
                     (Func
                          (Func
                               (Func
                                    (Func (Plus (Var Here)
                                                (Plus (Var (There Here))
                                                      (Plus (Var (There (There Here)))
                                                            (Plus (Var (There (There (There Here))))
                                                                  (Plus (Var (There (There (There (There Here)))))
                                                                        (Plus  (Var (There (There (There (There (There Here))))))
                                                                               (Var (There (There (There (There (There (There Here)))))))
                                                                        )
                                                                  )
                                                            )
                                                      )
                                                 )
                                          )
                                    )
                               )
                          )
                     )
                )
            )
       )
