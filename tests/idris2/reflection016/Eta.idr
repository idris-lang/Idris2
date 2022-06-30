import Language.Reflection

%default total

%language ElabReflection

x : List String
x = ["a", "b"]

infixl 1 >==>

-- From prelude:
--(>=>) : Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
--(>=>) f g = \x => f x >>= g

(>==>) : Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
(>==>) f g = \x => f x >>= \r => g r

%runElab traverse_ (pure >==> logMsg "debug" 0) x
%runElab traverse_ (pure >=> \s => logMsg "debug" 0 s) x
%runElab traverse_ (pure >=> logMsg "debug" 0) x

testing0 : Bool -> Elab String
testing0 False = pure "This is false"
testing0 True = pure "this is true"

testing1 : String -> Elab ()
testing1 x = logMsg x 0 "debug"

%runElab traverse_ (testing0 >=> testing1) [False, True]
