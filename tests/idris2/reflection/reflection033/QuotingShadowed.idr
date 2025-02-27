module QuotingShadowed

import Data.Vect

import Language.Reflection

%language ElabReflection

X : (Nat -> Nat) -> Type
X f = Vect (f 2) Unit

--------------------------
--- Shadowing using UN ---
--------------------------

-- (x : Nat) -> (y : X (\x -> S x)) -> Nat
tyExpr : TTImp
tyExpr =
  IPi EmptyFC MW ExplicitArg (Just `{x}) `(Prelude.Types.Nat) $
  IPi EmptyFC MW ExplicitArg (Just `{y}) (
    IApp EmptyFC `(QuotingShadowed.X) $
      ILam EmptyFC MW ExplicitArg (Just $ UN $ Basic "x") `(Prelude.Types.Nat) $
        IApp EmptyFC `(Prelude.Types.S) $ IVar EmptyFC `{x}
  ) $
  `(Prelude.Types.Nat)

ty : Elab Type
ty = check tyExpr

T : Type
T = %runElab ty

f : T
f n [(), (), ()] = 4

--------------------------------
--- Pseudo-shadowing with MN ---
--------------------------------

tyExpr' : TTImp
tyExpr' =
  IPi EmptyFC MW ExplicitArg (Just `{x}) `(Prelude.Types.Nat) $
  IPi EmptyFC MW ExplicitArg (Just `{y}) (
    IApp EmptyFC `(QuotingShadowed.X) $
      ILam EmptyFC MW ExplicitArg (Just $ MN "x" 0) `(Prelude.Types.Nat) $
        IApp EmptyFC `(Prelude.Types.S) $ IVar EmptyFC `{x}
  ) $
  `(Prelude.Types.Nat)

ty' : Elab Type
ty' = check tyExpr'

T' : Type
T' = %runElab ty'

f' : T'
f' Z     [()]     = 4
f' (S x) (()::xs) = S $ f' x xs

--------------------------------
--- Requoted the one with UN ---
--------------------------------

tyExpr'' : TTImp
tyExpr'' = %runElab quote T

ty'' : Elab Type
ty'' = check tyExpr''

T'' : Type
T'' = %runElab ty''

f'' : T''
f'' n [(), (), ()] = 4

-- check that T'' has really `MN _ 0` --

N'' : Nat
N'' = case tyExpr'' of
        (IPi _ _ _ _ _ $ IPi _ _ _ _ (IApp _ _ $ ILam _ _ _ (Just n) _ _) _) =>
          case n of
            UN _     => 1
            MN "x" 0 => 2
            _        => 3
        _ => 0

n''value : N'' = 2
n''value = Refl

--------------------
--- Printing out ---
--------------------

%runElab logSugaredTerm "shdw" 0 "tyExpr  " tyExpr
%runElab logSugaredTerm "shdw" 0 "tyExpr' " tyExpr'
%runElab logSugaredTerm "shdw" 0 "tyExpr''" tyExpr''

%runElab logSugaredTerm "shdw" 0 "quoted T  " !(quote T  )
%runElab logSugaredTerm "shdw" 0 "quoted T' " !(quote T' )
%runElab logSugaredTerm "shdw" 0 "quoted T''" !(quote T'')
