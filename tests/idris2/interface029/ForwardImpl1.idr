
interface Pretty a where
    pretty : a -> String

data Bar : Type -> Type
data Foo a = FNil | FCons a (Bar a)
data Bar a = BNil | BCons a (Foo a)

Pretty a => Pretty (Foo a)

implementation Pretty a => Pretty (Bar a) where
    pretty (BNil) = "Nil"
    pretty (BCons a f) = "\{pretty a} :: \{pretty f}"

implementation Pretty a => Pretty (Foo a) where
    pretty (FNil) = "Nil"
    pretty (FCons a f) = "\{pretty a} :: \{pretty f}"

implementation Pretty String where
    pretty a = a

main : IO ()
main = putStrLn $ pretty (BCons "1" (FCons "2" (BCons "3" FNil)))
