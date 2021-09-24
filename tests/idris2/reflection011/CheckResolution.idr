import Language.Reflection

%language ElabReflection

checkWithoutLambda : Integer
checkWithoutLambda = %runElab (do
  x <- check (IPrimVal EmptyFC (BI 3))
  pure x)

checkWithLambda : Integer -> Integer
checkWithLambda = %runElab (lambda Integer $ \v => do
  x <- check (IPrimVal EmptyFC (BI 3))
  pure $ v + x)
