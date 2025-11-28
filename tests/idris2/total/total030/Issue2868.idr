%default total

namespace Foo
  public export
  total
  foo : ()

namespace Bar
  public export
  total
  bar : ()

namespace Foo
  foo = bar

namespace Bar
  bar = foo
