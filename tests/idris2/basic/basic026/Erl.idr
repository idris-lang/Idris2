data ErlList : List Type -> Type where
  Nil : ErlList []
  (::) : x -> ErlList xs -> ErlList (x :: xs)

data ErlType : Type -> Type where
  ETInteger : ErlType Integer
  ETString : ErlType String

data ErlTypes : List Type -> Type where
  ETErlTypesNil : ErlTypes []
  ETErlTypesCons : (ErlType x, ErlTypes xs) => ErlTypes (x :: xs)

erlCall : ErlList xs -> {auto prf : ErlTypes xs} -> ()
erlCall args = ()

foo : ()
foo = erlCall [1,2,3, "foo", "bar", "baz", 4,5,6]
