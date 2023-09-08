data Gnu : Type where [noHints, uniqueSearch]
  ||| Use Bool stop proof search from using constructors
  G : Bool -> Gnu
  N : Bool -> Gnu
  U : Bool -> Gnu

||| Makes interaction a bit nicer
Show Gnu where
  show (G _) = "G"
  show (N _) = "N"
  show (U _) = "U"

FooG : Gnu
FooG = G True

FooN : Gnu
FooN = N True

FooU : Gnu
FooU = U True

||| Curried versions
CooG : Unit -> Gnu
CooG _ = FooG

CooN : Unit -> Gnu
CooN _ = FooN

CooU : Unit -> Gnu
CooU _ = FooU

||| We'll use this to see what proof Idris finds.
Guess : {auto gnu : Gnu} -> String
Guess {gnu} = show gnu

||| Calls `Guess {gnu = gnu}` as expected
TestOK1 : (gnu : Gnu) -> String
TestOK1 gnu = Guess

||| Calls `Guess {gnu = f ()}` as expected
TestOK2 : (f : Unit -> Gnu) -> String
TestOK2 f = Guess

||| This is the meat. I'd expect this function to raise an error
||| because it is ambiguous which local/local function to use.
TestSurprise1 : (gnu1, gnu2 : Gnu) -> String
TestSurprise1 gnu1 gnu2 = Guess

TestSurprise2 : (f,g : Unit -> Gnu) -> String
TestSurprise2 f g = Guess

TestSurprise3 : (Unit -> Gnu, Unit -> Gnu) -> String
TestSurprise3 f = Guess
