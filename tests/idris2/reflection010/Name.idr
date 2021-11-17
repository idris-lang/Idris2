import Language.Reflection

%language ElabReflection

%logging 1

-- This test is for checking changes to how Names are reflected and reified.
-- It currently tests Names that refer to nested functions and Names that refer
-- to nested cases.

-- Please add future tests for Names here if they would fit in. There's plenty
-- of room.

data Identity a = MkIdentity a

nested : Identity Int
nested = MkIdentity foo
  where
    foo : Int
    foo = 12

-- a pattern matching lambda is really a case
cased : Identity Int -> Int
cased = \(MkIdentity x) => x

test : Elab ()
test = do
    n <- quote nested
    logTerm "" 1 "nested" n
    MkIdentity n' <- check {expected=Identity Int} n
    logMsg "" 1 $ show (n' == 12)

    c <- quote cased
    logTerm "" 1 "cased" c
    c' <- check {expected=Identity Int -> Int} c
    logMsg "" 1 $ show (c' (MkIdentity 10))

    pure ()

%runElab test
