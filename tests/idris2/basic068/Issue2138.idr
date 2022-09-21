
namespace Foo

  public export
  data T
    = A Int
    | B T

  export
  Show T where
    show (A n) = "[A " ++ show n ++ "]"
    show (B t) = "[B " ++ show t ++ "]"

namespace Bar

  %hide Foo.T

  public export
  data T
    = A Int
    | B T
    | C Bool

  export
  Show T where
    show (A n) = "{A " ++ show n ++ "}"
    show (B t) = "{B " ++ show t ++ "}"
    show (C b) = "{C " ++ show b ++ "}"

  %unhide Foo.T

foo : Foo.T
foo = B (A 5)

bar : Bar.T
bar = B (A 6)

main : IO ()
main = do
  printLn foo
  printLn bar
