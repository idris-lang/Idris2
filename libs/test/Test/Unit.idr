module Test.Unit

Test : Type -> Type
Test a = a -> Bool

isUnit : Test Unit
isUnit unit = unit == ()
