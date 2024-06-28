import Language.Reflection

%default total

scr : ty -> ty -> Elab ty
scr l r = do
  Just x <- search $ Semigroup ty
    | Nothing => pure l
  pure $ l <+> r

%language ElabReflection

data N = A | B | C | D

X : N
X = %runElab scr B C

xCorr : X = B
xCorr = Refl

Y : List Nat
Y = %runElab scr [1, 2, 3] [4, 5]

yCorr : Y = [1, 2, 3, 4, 5]
yCorr = Refl
