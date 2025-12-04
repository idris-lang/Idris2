%default total

namespace Foo
  public export
  foo : Void

namespace Bar
  public export
  bar : Void
  bar = foo

namespace Foo
  foo = bar

boom : Void
boom = foo
