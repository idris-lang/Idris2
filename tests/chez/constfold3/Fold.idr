public export
data Singleton : {0 a : Type} -> (x : a) -> Type where
  MkSingleton : (x : a) -> Singleton x

Show a => Show (Singleton {a} v) where show (MkSingleton v) = show v

export
unsafeMkSingleton : (y : a) -> Singleton {a} x
unsafeMkSingleton y = believe_me (MkSingleton y)

main : IO ()
main = printLn $ unsafeMkSingleton {x = 12} (S Z)
