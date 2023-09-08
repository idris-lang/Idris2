import Language.Reflection

%language ElabReflection

data NatExpr : Nat -> Type where
     Plus : NatExpr x -> NatExpr y -> NatExpr (plus x y)
     Mult : NatExpr x -> NatExpr y -> NatExpr (mult x y)
     Dbl : NatExpr x -> NatExpr (mult 2 x)
     Val : (val : Nat) -> NatExpr val

getNatExpr : TTImp -> Elab (n ** NatExpr n)
getNatExpr `(Prelude.Types.plus ~(x) ~(y))
   = do (_ ** xval) <- getNatExpr x
        (_ ** yval) <- getNatExpr y
        pure (_ ** Plus xval yval)
getNatExpr `(Prelude.Types.mult (Prelude.Types.S (Prelude.Types.S Prelude.Types.Z)) ~(y))
   = do (y ** yval) <- getNatExpr y
        pure (_ ** Dbl yval)
getNatExpr `(Prelude.Types.mult ~(x) ~(y))
   = do (_ ** xval) <- getNatExpr x
        (_ ** yval) <- getNatExpr y
        pure (_ ** Mult xval yval)
getNatExpr x = pure (_ ** Val !(check x))

%macro
mkNatExpr : (n : Nat) -> Elab (NatExpr n)
mkNatExpr n
    = do Just `(Main.NatExpr ~(expr)) <- goal
              | _ => fail "Goal is not a NatExpr"
         (n' ** expr') <- getNatExpr expr
         check !(quote expr')

test1 : (x : Nat) -> (y : Nat) -> NatExpr (plus x (plus y x))
test1 x y = mkNatExpr _ -- yes, auto implicits can do this too :)

test2 : (x : Nat) -> (y : Nat) -> NatExpr (plus x (mult y x))
test2 x y = mkNatExpr _

test3 : (x : Nat) -> (y : Nat) -> NatExpr (plus x (mult 2 x))
test3 x y = mkNatExpr _ -- auto implicit search gets something different
