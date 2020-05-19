||| Test extended record syntax
data NotZero : Nat -> Type where
  Is : {n : Nat} -> NotZero (S n)

record Positive (n : Nat) {auto 0 pos : NotZero n} where
  constructor Check

a : Positive 1
a = Check

b : Positive 2
b = Check

{- Will not type-check
c : Positive 0
-}

data KindOfString = ASCII | UTF

UTForASCII : KindOfString -> Type
UTForASCII UTF = String
UTForASCII ASCII = List Char   --- Just to demonstrate

record FlexiString { default UTF k : KindOfString} where
  constructor MkFlexiString
  val : UTForASCII k
  
c : FlexiString
c = MkFlexiString "hello"

d : FlexiString {k = ASCII}
d = MkFlexiString ['h', 'i']

