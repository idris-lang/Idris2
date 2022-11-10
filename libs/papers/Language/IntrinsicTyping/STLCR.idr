||| The content of this module is based on the MSc Thesis
||| Coinductive Formalization of SECD Machine in Agda
||| by Adam Krupička

module Language.IntrinsicTyping.STLCR

import Data.List.Elem
import Language.IntrinsicTyping.SECD

%default total

public export
data STLCR : List (Ty, Ty) -> List Ty -> Ty -> Type where
  Var : Elem ty g -> STLCR r g ty
  Lam : STLCR ((a, b) :: r) (a :: g) b -> STLCR r g (TyFun a b)
  App : {a : _} -> STLCR r g (TyFun a b) -> STLCR r g a -> STLCR r g b
  Rec : Elem (a,b) r -> STLCR r g (TyFun a b)
  If  : STLCR r g TyBool -> (t, f : STLCR r g a) -> STLCR r g a
  Eqb : {a : _} -> STLCR r g a -> STLCR r g a -> STLCR r g TyBool
  Lit : Const ty -> STLCR r g ty
  Add, Sub, Mul : (m, n : STLCR r g TyInt) -> STLCR r g TyInt

public export
fromInteger : Integer -> STLCR r g TyInt
fromInteger n = Lit (AnInt (cast n))

factorial : STLCR [] [] (TyFun TyInt TyInt)
factorial
  = Lam $ If (Eqb (Var Here) 0)
      1
      (Mul (Var Here) (App (Rec Here) (Sub (Var Here) 1)))

public export
compile : {ty : _} -> STLCR r g ty -> MkState s g r `Steps` MkState (ty :: s) g r

public export
compileT : {b : _} -> STLCR ((a, b) :: r) (a :: g) b ->
           MkState [] (a :: g) ((a, b) :: r) `Steps` MkState [b] (a :: g) ((a, b) :: r)

public export
compileAcc : {ty : _} -> init `Stepz` MkState s g r -> STLCR r g ty -> init `Stepz` MkState (ty :: s) g r
compileAcc acc (Var v) = acc :< LDA v
compileAcc acc (Lam b) = acc :< LDF (compileT b)
compileAcc acc (App f t) = compileAcc (compileAcc acc f) t :< APP
compileAcc acc (Rec v) = acc :< LDR v
compileAcc acc (If b t f) = compileAcc acc b :< BCH (compile t) (compile f)
compileAcc acc (Eqb x y) = compileAcc (compileAcc acc y) x :< EQB
compileAcc acc (Lit c) = acc :< LDC c
compileAcc acc (Add m n) = compileAcc (compileAcc acc n) m :< ADD
compileAcc acc (Sub m n) = compileAcc (compileAcc acc n) m :< SUB
compileAcc acc (Mul m n) = compileAcc (compileAcc acc n) m :< MUL

compile t = compileAcc [<] t <>> []

compileT (Lam b) = [LDF (compileT b)]
compileT (App f t) = compileAcc (compileAcc [<] f) t <>> [TAP]
compileT (If b t f) = compileAcc [<] b <>> [BCH (compileT t) (compileT f)]
compileT (Lit c) = [LDC c]
compileT t = compileAcc [<] t <>> [RTN]


testPLS : compile (Lam (Lam (Add (Var (There Here)) (Var Here))))
      === [LDF [LDF [LDA Here, LDA (There Here), ADD, RTN]]]
testPLS = Refl

testFAC : run (compile (App STLCR.factorial 5)) 12 === Just 120
testFAC = Refl
